use ark_bn254::{Fq, Fq12, Fq2, Fr, G1Affine, G2Affine};
use num_bigint::BigUint;
use sha2::Digest;

pub struct Transcript {
    state: [u8; 32],
}

impl Transcript {
    pub fn new() -> Self {
        Transcript { state: [0u8; 32] }
    }

    pub fn append(&mut self, message: &[u8]) {
        let old_state = self.state;
        let mut hasher = sha2::Sha256::new();
        hasher.update(&old_state);
        hasher.update(message);
        let mut result = [0u8; 32];
        result.copy_from_slice(&hasher.finalize());
        self.state = result;
    }

    pub fn append_fq(&mut self, x: Fq) {
        let u8_vec = from_fq_to_u8(x);
        self.append(&u8_vec);
    }

    pub fn append_fq2(&mut self, x: Fq2) {
        let u8_vec = from_fq2_to_u8(x);
        self.append(&u8_vec);
    }

    pub fn append_fq12(&mut self, x: Fq12) {
        let u8_vec = from_fq12_to_u8(x);
        self.append(&u8_vec);
    }

    pub fn append_g1(&mut self, x: G1Affine) {
        let x_u8 = from_fq_to_u8(x.x);
        let y_u8 = from_fq_to_u8(x.y);
        self.append(&[x_u8, y_u8].concat());
    }

    pub fn append_g2(&mut self, x: G2Affine) {
        let x_u8 = from_fq2_to_u8(x.x);
        let y_u8 = from_fq2_to_u8(x.y);
        self.append(&[x_u8, y_u8].concat());
    }

    pub fn get_challenge(&self) -> Fr {
        let mut hasher = sha2::Sha256::new();
        hasher.update(&self.state);
        let mut result = [0u8; 32];
        result.copy_from_slice(&hasher.finalize());
        let b = BigUint::from_bytes_le(&result);
        b.into()
    }
}

fn from_fq_to_u8(x: Fq) -> Vec<u8> {
    let b: BigUint = x.into();
    b.to_bytes_le()
}

fn from_fq2_to_u8(x: Fq2) -> Vec<u8> {
    let c0 = x.c0;
    let c1 = x.c1;
    let fq_vec = vec![c0, c1];
    let mut u8_vec = Vec::new();
    for fq in fq_vec {
        u8_vec.extend(from_fq_to_u8(fq));
    }
    u8_vec
}

fn from_fq12_to_u8(x: Fq12) -> Vec<u8> {
    let c0 = x.c0;
    let c1 = x.c1;
    let c00 = c0.c0;
    let c01 = c0.c1;
    let c02 = c0.c2;
    let c10 = c1.c0;
    let c11 = c1.c1;
    let c12 = c1.c2;
    let fq2_vec = vec![c00, c01, c02, c10, c11, c12];
    let mut u8_vec = Vec::new();
    for fq in fq2_vec {
        u8_vec.extend(from_fq2_to_u8(fq));
    }
    u8_vec
}
