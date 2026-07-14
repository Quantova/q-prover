//! The qtv-stark crate holds the hash based STARK backend for Quantova.
//!
//! It provides prime field arithmetic, Merkle commitments, FRI folding, and the
//! prover and verifier interfaces. Every proof rests on hashing alone. There are
//! no pairings and no elliptic curve operations anywhere in this crate.

pub mod air;
pub mod batch;
pub mod decompose;
pub mod examples;
pub mod field;
pub mod fri;
pub mod hashing;
pub mod hint;
pub mod keccak;
pub mod lattice;
pub mod merkle;
pub mod norm;
pub mod ntt;
pub mod poly;
pub mod prover;
pub mod sample;
pub mod sponge;
pub mod stark;
pub mod verifier;
