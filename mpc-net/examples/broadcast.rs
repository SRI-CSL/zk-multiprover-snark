use log::debug;
use mpc_net::multi;

use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "example", about = "An example of StructOpt usage.")]
struct Opt {
    /// Id
    id: usize,

    /// Input file
    #[structopt(parse(from_os_str))]
    input: PathBuf,
}

fn main() {
    env_logger::builder().format_timestamp(None).format_module_path(false).init();
    debug!("Start");
    let opt = Opt::from_args();
    println!("{:?}", opt);
    multi::init_from_path(opt.input.to_str().unwrap(), opt.id);
    let all = multi::broadcast(&[opt.id as u8]);
    println!("{:?}", all);
    multi::uninit();
}