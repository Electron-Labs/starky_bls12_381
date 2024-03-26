# STARKY BLS 12-381
MVP implementation of bls12-381 in starky and plonky2

## Architecture
Starting from G1 and G2 points, the BLS12-381 signature verification algorithm has 4 steps: 2 miller loop computation steps, 1 Fp12 multiplication, and 1 final exponentiation step.
The miller loop computation within itself has two steps: calculating precomputes, followed by the loop itself.

Hence, we have 4 separate starks for each of these operations:
* PairingPrecompStark
* MillerLoopStark
* FP12MulStark
* FinalExponentiateStark

The algorithm is proved using six starky proofs: 2 for the first miller loop (1 PairingPrecompStark proof and 1 MillerLoopStark proof), 2 for the second miller loop, 1 for FP12 multiplication, and 1 for the final exponentiation step.

After computing the stark proofs, we recursively prove each of the starky proof inside plonky2 to get six separate plonky2 proofs. Then we perform another recursion step which combines and links all the previous six plonky2 proofs, hence proving the complete BLS12-381 signature verification.

## Documentation

For now, the codebase has explanatory comments, and doc comments in each of the stark trace and constraint generation functions. We have defined offsets for columns of the trace, and use these offsets for generating the trace and adding the constraints. Explanation of the offsets is also present as comments.

## How to run

We need to increase the default rust stack size because of the high number of columns in some of the traces. 16MB stack size is sufficient.

`RUST_MIN_STACK=16777216 cargo run --release`

Note: Currently the program takes a long time to run because we build the plonky2 circuits each time. We plan to build and store these circuits, while also parallelise the stark proof generation and first recursion step to make it more performant.

## Performance

On AWS r6a.8xlarge machine:

|Stark|Columns|Rows|Starky proving time|Plonky2 recursive gates|Plonky2 recursive build time|Plonky2 recursive proving time|
|:-----|-------:|----:|------------------:|-----------------------:|----------------------------:|------------------------------:|
|PairingPrecompStark|29376|1024|~4.5s|502790|~50s|~43s|
|MillerLoopStark|97330|1024|~12.5s|1536789|~242s|~185s|
|FP12MulStark|60285|16|~220ms|947380|~114s|~92s|
|FinalExponentiateStark|73527|8192|~92s|1284720|~274s|~185s|
|ECCAggregate|3339|8192|~3s|64155|~10.3s|~6.2s|

For the aggregate plonky2 circuit:
* Gates - 1284720
* Build time - ~100s
* Proving time - ~63s

## Developer chat
This work is convered under Ethereum Foundation grant. In case you wish to contribute or collaborate, you can join our ZK builder chat at - https://t.me/+leHcoDWYoaFiZDM1
