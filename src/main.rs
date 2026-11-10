mod machine;
mod parsing;
mod storage;
mod term;
mod types;


use color_print::cprintln;
use nom_language::error::convert_error;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

use crate::machine::{InputStack, OutputStack, State};
use crate::parsing::parse_term;
use crate::storage::{Storage, WithStorage};
use crate::types::{typecheck, TypingContext};

pub const DEFAULT_STACK_ID: &'static str = "Lambda";
pub const EMPTY_STACK_SYMBOL: &'static str = "Eps";
pub const EMPTY_SUM_SYMBOL: &'static str = "0";

use clap::Parser;

#[derive(Parser)]
pub struct Args {
    #[arg(default_value_t = "".into())]
    pub input: String,
}

fn run_program(source: String) {
    let storage = Storage::default();

    let t = match parse_term(&source, &storage) {
        Ok((_, t)) => t,
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => {
            cprintln!("<red>Parse error</>: {}", convert_error(source.as_str(), e));
            return;
        }
        Err(e) => {
            cprintln!("<red>Parse error</>: {e}");
            return;
        }
    };
    cprintln!("<green>Parsed</>: <yellow>{}</>", WithStorage(&t, &storage));

    match typecheck(&t, &mut TypingContext::default(), &storage) {
        Ok(ty) => {
            cprintln!("<green>Type</>: <cyan>{}</>", WithStorage(&ty, &storage));
        }
        Err(e) => {
            cprintln!("<red>Type error</>: {e}");
            return;
        }
    }

    let mut state = State::new(t);
    state.register_stack(&storage, "input", InputStack);
    state.register_stack(&storage, "output", OutputStack);

    cprintln!("<dim>{}</>", WithStorage(&state, &storage));

    loop {
        if state.is_final() {
            cprintln!("<green>Success</>");
            break;
        }
        if state.is_failure() {
            cprintln!("<red>Failure</>");
            break;
        }
        state = state
            .transition(&storage)
            .expect("state should have a transition");
        println!("--------------------");
        cprintln!("<dim>{}</>", WithStorage(&state, &storage));
    }
}

const HISTORY_PATH: &'static str = ".fmc-history";

fn main() -> anyhow::Result<()> {
    let args = Args::parse();

    let mut rl = DefaultEditor::new()?;
    rl.load_history(HISTORY_PATH).ok();

    if args.input.is_empty() {
        loop {
            let line = match rl.readline("> ") {
                Ok(line) => {
                    rl.add_history_entry(line.as_str())?;
                    line
                }
                Err(ReadlineError::Interrupted) => {
                    println!("^C");
                    break;
                }
                Err(ReadlineError::Eof) => {
                    println!("^D");
                    break;
                }
                Err(err) => {
                    println!("<red>error</>: {:?}", err);
                    break;
                }
            };
            rl.save_history(HISTORY_PATH)?;
            run_program(line);
        }
    } else {
        run_program(std::fs::read_to_string(&args.input)?);
    }

    Ok(())
}
