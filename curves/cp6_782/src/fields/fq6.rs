use crate::{Fq, Fq3, Fq3Parameters, FQ_ONE, FQ_ZERO};
use ark_ff::{
    field_new,
    fields::fp6_2over3::{Fp6, Fp6Parameters},
};

pub type Fq6 = Fp6<Fq6Parameters>;

pub struct Fq6Parameters;

impl Fp6Parameters for Fq6Parameters {
    type Fp3Params = Fq3Parameters;

    /// NONRESIDUE = (0, 1, 0).
    #[rustfmt::skip]
    const NONRESIDUE: Fq3 = field_new!(Fq3, FQ_ZERO, FQ_ONE, FQ_ZERO);

    #[rustfmt::skip]
    const FROBENIUS_COEFF_FP6_C1: &'static [Fq] = &[
        field_new!(Fq, "1"),
        field_new!(Fq, "2416169158604010336818399199316106389588878314690767988978701685873498866746813334102117883272276610365242925950967572554030909749205624998805208910209389668659757274773858916683688639755413288353778854399286396639505385648830027756862"),
        field_new!(Fq, "2416169158604010336818399199316106389588878314690767988978701685873498866746813334102117883272276610365242925950967572554030909749205624998805208910209389668659757274773858916683688639755413288353778854399286396639505385648830027756861"),
        field_new!(Fq, "22369874298875696930346742206501054934775599465297184582183496627646774052458024540232479018147881220178054575403841904557897715222633333372134756426301062487682326574958588001132586331462553235407484089304633076250782629492557320825576"),
        field_new!(Fq, "19953705140271686593528343007184948545186721150606416593204794941773275185711211206130361134875604609812811649452874332003866805473427708373329547516091672819022569300184729084448897691707139947053705234905346679611277243843727293068715"),
        field_new!(Fq, "19953705140271686593528343007184948545186721150606416593204794941773275185711211206130361134875604609812811649452874332003866805473427708373329547516091672819022569300184729084448897691707139947053705234905346679611277243843727293068716"),
    ];
}