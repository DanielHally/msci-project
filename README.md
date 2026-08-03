# msci-project

An Idris 2 embedded DSL for parsing binary data, based on Fisher et al.'s Data Description Calculus. Created for my MSci individual project at the University of Glasgow, supervised by Simon Fowler.

See the [dissertation](dissertation.pdf) for further information.

The recommended way to run this project is to install [idris2-pack](https://github.com/stefan-hoeck/idris2-pack), which allows code to be opened in a REPL using `pack repl path/to/file.idr`. From here, expressions can be evaluated by typing them, and IO monads can be executed using the `:exec` command.

## Structure

- The DDC directory contains all code defining the DSL itself, exposed for importing through the top-level DDC.idr file.
    - DSL.idr defines the core data structure and its host-language representation types
    - Error.idr provides the types used in error handling
    - Parse.idr and Serialisation.idr define the DSL’s parsing and representation semantics respectively
    - Binary.idr contains utilities for working with data as vectors of bits
    - BaseTypes.idr provides some base type implementations for use with the DSL
    - Ascii.idr defines utilities for working with ASCII-only strings
    - Helpers for writing in the DSL are defined in Syntax.idr and SequenceUtils.idr
    - Show.idr defines debug printing for parse resutls
    - Util.idr contains various utility functions not tied to the DSL itself
- The PacketLang directory contains the EDSL embedding of PacketLang, exposed for importing through PacketLang.idr.
- The Examples directory contains the code used in the evaluation of the project for parsing PNG and PacketLang-embedded DNS.
