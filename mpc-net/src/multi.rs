use lazy_static::lazy_static;
use log::debug;
use rayon::prelude::*;
use std::fs::File;
use std::io::{BufRead, BufReader, Read, Write};
use std::net::{SocketAddr, TcpListener, TcpStream};
use std::sync::Mutex;
//use crossbeam::scope;

#[macro_use]
lazy_static! {
    pub static ref CONNECTIONS: Mutex<Connections> = Mutex::new(Connections::default());
}

/// Macro for locking the FieldChannel singleton in the current scope.
macro_rules! get_ch {
    () => {
        CONNECTIONS.lock().expect("Poisoned FieldChannel")
    };
}

#[derive(Default)]
pub struct Stats {
    pub bytes_sent: u64,
    pub bytes_recv: u64,
    pub exchanges: u64,
}

pub struct Peer {
    pub id: usize,
    pub addr: SocketAddr,
    pub stream: Option<TcpStream>,
    pub stats: Stats,
}

#[derive(Default)]
pub struct Connections {
    pub id: usize,
    pub peers: Vec<Peer>,
    pub stats: Stats,
}

impl std::default::Default for Peer {
    fn default() -> Self {
        Self {
            id: 0,
            addr: "127.0.0.1:8000".parse().unwrap(),
            stream: None,
            stats: Default::default(),
        }
    }
}

impl Connections {
    /// Given a path and the `id` of oneself, initialize the structure
    fn init_from_path(&mut self, path: &str, id: usize) {
        let f = BufReader::new(File::open(path).expect("host configuration path"));
        let mut peer_id = 0;
        for line in f.lines() {
            let line = line.unwrap();
            let trimmed = line.trim();
            if trimmed.len() > 0 {
                let addr: SocketAddr = trimmed
                    .parse()
                    .unwrap_or_else(|e| panic!("bad socket address: {}:\n{}", trimmed, e));
                let peer = Peer {
                    id: peer_id,
                    addr,
                    stream: None,
                    stats: Default::default(),
                };
                self.peers.push(peer);
                peer_id += 1;
            }
        }
        assert!(id < self.peers.len());
        self.id = id;
    }
    fn connect_to_all(&mut self) {
        let n = self.peers.len();
        for from_id in 0..n {
            for to_id in (from_id + 1)..n {
                debug!("{} to {}", from_id, to_id);
                if self.id == from_id {
                    let to_addr = self.peers[to_id].addr;
                    debug!("Contacting {}", to_id);
                    let stream = loop {
                        let mut ms_waited = 0;
                        match TcpStream::connect(to_addr) {
                            Ok(s) => break s,
                            Err(e) => match e.kind() {
                                std::io::ErrorKind::ConnectionRefused
                                | std::io::ErrorKind::ConnectionReset => {
                                    ms_waited += 10;
                                    std::thread::sleep(std::time::Duration::from_millis(10));
                                    if ms_waited % 3_000 == 0 {
                                        debug!("Still waiting");
                                    } else if ms_waited > 30_000 {
                                        panic!("Could not find peer in 30s");
                                    }
                                }
                                _ => {
                                    panic!("Error during FieldChannel::new: {}", e);
                                }
                            },
                        }
                    };
                    stream.set_nodelay(true).unwrap();
                    self.peers[to_id].stream = Some(stream);
                } else if self.id == to_id {
                    debug!("Awaiting {}", from_id);
                    let listener = TcpListener::bind(self.peers[self.id].addr).unwrap();
                    let (stream, _addr) = listener.accept().unwrap();
                    stream.set_nodelay(true).unwrap();
                    self.peers[from_id].stream = Some(stream);
                }
            }
            // Sender for next round waits for note from this sender to prevent race on receipt.
            if from_id + 1 < n {
                if self.id == from_id {
                    self.peers[self.id + 1].stream.as_mut().unwrap().write_all(&[0u8]).unwrap();
                } else if self.id == from_id + 1 {
                    self.peers[self.id - 1].stream.as_mut().unwrap().read_exact(&mut [0u8]).unwrap();
                }
            }
        }
        for id in 0..n {
            if id != self.id {
                assert!(self.peers[id].stream.is_some());
            }
        }
    }
    fn am_king(&self) -> bool {
        self.id == 0
    }
    fn broadcast(&mut self, bytes_out: &[u8]) -> Vec<Vec<u8>> {
        let m = bytes_out.len();
        let own_id = self.id;
        self.peers
            .par_iter_mut()
            .enumerate()
            .map(|(id, peer)| {
                let mut bytes_in = vec![0u8; m];
                if id < own_id {
                    let stream = peer.stream.as_mut().unwrap();
                    stream.read_exact(&mut bytes_in[..]).unwrap();
                    stream.write_all(bytes_out).unwrap();
                } else if id == own_id {
                    bytes_in.copy_from_slice(bytes_out);
                } else {
                    let stream = peer.stream.as_mut().unwrap();
                    stream.write_all(bytes_out).unwrap();
                    stream.read_exact(&mut bytes_in[..]).unwrap();
                };
                bytes_in
            })
            .collect()
    }
    fn uninit(&mut self) {
        for p in &mut self.peers {
            p.stream = None;
        }
    }
}

pub fn init_from_path(path: &str, id: usize) {
    let mut ch = get_ch!();
    ch.init_from_path(path, id);
    ch.connect_to_all();
    debug!("Connected");
}

pub fn broadcast(bytes_out: &[u8]) -> Vec<Vec<u8>> {
    get_ch!().broadcast(bytes_out)
}

pub fn am_king() -> bool {
    get_ch!().am_king()
}

pub fn uninit() {
    get_ch!().uninit();
    debug!("Unconnected");
}