#!/bin/sh
cargo build --release
perf stat target/release/bt 19
