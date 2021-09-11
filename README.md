# collections-ext
## Table of Contents
<!-- TOC -->

- [collections-ext](#collections-ext)
	- [Table of Contents](#table-of-contents)
	- [General](#general)
		- [Note](#note)
	- [Usage](#usage)
		- [Testing](#testing)
			- [Benchmark tests](#benchmark-tests)
		- [Features](#features)
	- [Warnings](#warnings)

<!-- /TOC -->

## General
This repo is intended to function as a catch-all bucket for datastructures that I am working with for side projects and learning purposes.

### Note
All collections must function without a need for stdlib by default.

## Usage
### Testing
Tests and documentation are provided primarily via docstring examples primarily but a few tests are additionally provided through standard rust unit testing and can be run via:

```
cargo test
```

#### Benchmark tests
Additionally benchmark tests are provided via `criterion` and can be run via:

```
cargo bench
```

### Features

- `std`: Enable the standard library. Disabled by default for core.

## Warnings
Please nobody use this. This is entirely an experiment to support insane restrictions I've imposed on myself to build a computer from first principles.