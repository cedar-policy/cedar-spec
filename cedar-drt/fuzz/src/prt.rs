/*
 * Copyright Cedar Contributors. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#[cfg(feature = "prt")]
#[macro_export]
macro_rules! fuzz_target {
    (|$data:ident: $dty: ty| $body:block) => {
        // Arguments
        use clap::Parser;
        use rayon::prelude::*;
        use std::path::PathBuf;

        #[derive(Parser, Debug)]
        struct Args {
            /// Number of iterations
            #[arg(short, long, default_value_t = u64::MAX)]
            runs: u64,

            /// The root path to write corpus tests
            #[arg(short, long, value_name = "DIR")]
            path: Option<PathBuf>,

            /// Random seed (use OS-generated number if none is provided)
            #[arg(short, long)]
            seed: Option<u64>,

            /// Number of threads (default to system max)
            #[arg(short, long, default_value_t = rayon::current_num_threads())]
            thread_num: usize,

            /// Random byte size
            #[arg(short, long, default_value_t = 1024)]
            byte_size: u16,
        }

        // The little trick to have main function when `#[no_main]` is enabled.
        #[no_mangle]
        pub extern "C" fn main() {
            let args = Args::parse();
            let seed = args.seed.unwrap_or_else(|| rand::random::<u64>());
            let runs = args.runs;

            let prt_test_target = |corpus_dir: Option<std::path::PathBuf>, id: u64| {
                use rand_chacha::{
                    rand_core::{RngCore, SeedableRng},
                    ChaCha8Rng,
                };
                use std::io::Write;

                let mut rng = ChaCha8Rng::seed_from_u64(seed);
                rng.set_stream(id);

                for r in 0..runs {
                    // We need a fixed random byte size because the generation process depends on the size of random bytes.
                    let size = args.byte_size as usize;
                    let mut bytes: Vec<u8> = vec![0; size];
                    // generate randomized data
                    rng.fill_bytes(&mut bytes);
                    let mut u = Unstructured::new(&bytes);
                    // create a randomized structured input
                    let data = <$dty as Arbitrary>::arbitrary(&mut u);
                    log::info!("total cost: {}", size - u.len());

                    // ``fail fast'' if the construction is unsucessful
                    let $data = match data {
                        Ok(d) => d,
                        Err(e) => {
                            log::debug!("{id}, run: {} err: {:?}", r, e);
                            continue;
                        }
                    };
                    if let Some(dir) = &corpus_dir {
                        let mut input_file =
                            std::fs::File::create(dir.join(format!("{}-{}", id, r)))
                                .expect("A corpus test file should be creatable!");
                        input_file
                            .write_all(&bytes)
                            .expect("We should be able to write to a corpus test file!");
                    }
                    $body
                }
            };

            let num_threads = args.thread_num as u64;
            let pool = rayon::ThreadPoolBuilder::new()
                .num_threads(args.thread_num)
                .build()
                .unwrap();

            // create directories
            if let Some(path) = &args.path {
                (0..num_threads).into_iter().for_each(|i| {
                    std::fs::create_dir_all(
                        std::path::Path::new(path).join(&format!("corpus-{}", i % num_threads)),
                    )
                    .expect("Corpus directory should exist or creatable!");
                });
            }
            pool.install(|| {
                (0..num_threads).into_par_iter().for_each(|i| {
                    prt_test_target(
                        args.path
                            .as_ref()
                            .map(|p| std::path::Path::new(&p).join(&format!("corpus-{}", i))),
                        i,
                    );
                });
            });
        }
    };
}

#[cfg(feature = "log")]
#[macro_export]
macro_rules! fuzz_target {
    (|$data:ident: $dty: ty| $e:expr) => {
        libfuzzer_sys::fuzz_target! {
            | x : $dty| {
                use std::fs::OpenOptions;
                use std::io::prelude::*;
                use std::str::FromStr;
                use rand::{thread_rng, Rng};
                use serde::Serialize;
                let should_sample = if let Ok(rate_str) = std::env::var("RATE") {
                    let rate = u32::from_str(&rate_str).unwrap();
                    let mut rng = thread_rng();
                    let n:u32 = rng.gen_range(0..=100);
                    n < rate
                } else {
                    false
                };
                if should_sample {
                    let mut f = OpenOptions::new().write(true).append(true).create(true).open(std::env::var("LOGFILE").unwrap()).unwrap();
                    serde_json::to_writer(f, &x).unwrap();
                }
                let internal = |$data : $dty| $e;
                internal(x);
            }
        }
    }
}

#[cfg(not(feature = "prt"))]
#[cfg(not(feature = "log"))]
pub use libfuzzer_sys::fuzz_target;
