//! The qtv-stark crate holds the hash based STARK backend for Quantova.
//!
//! It provides prime field arithmetic, Merkle commitments, FRI folding, and the
//! prover and verifier interfaces. Every proof rests on hashing alone. There are
//! no pairings and no elliptic curve operations anywhere in this crate.

pub mod air;
pub mod examples;
pub mod field;
pub mod fri;
pub mod lattice;
pub mod merkle;
pub mod poly;
pub mod prover;
pub mod stark;
pub mod verifier;
