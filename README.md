# **Semantic Tableaux for Propositional and First-Order Logic** <!-- omit in toc -->

- [1. Introduction](#1-introduction)
- [2. Installation](#2-installation)
  - [2.1. Install Rust](#21-install-rust)
  - [2.2. Clone the repository](#22-clone-the-repository)
  - [2.3. Build the optimized executable](#23-build-the-optimized-executable)
- [3. Running the Program](#3-running-the-program)
  - [3.1. Basic syntax](#31-basic-syntax)
- [4. Language Syntax](#4-language-syntax)
  - [4.1. Propositional Connectives](#41-propositional-connectives)
  - [4.2. Predicates and Terms (FOL)](#42-predicates-and-terms-fol)
  - [4.3. Quantifiers (FOL)](#43-quantifiers-fol)
    - [4.3.1. Universal quantifier:](#431-universal-quantifier)
    - [4.3.2. Existential quantifier:](#432-existential-quantifier)
- [5. Usage Examples](#5-usage-examples)
  - [5.1. Arguments](#51-arguments)
    - [How to Pass This to the Program](#how-to-pass-this-to-the-program)
      - [Using Implication (Recommended)](#using-implication-recommended)
  - [5.2. Propositional logic](#52-propositional-logic)
  - [5.3. Valid formula in FOL](#53-valid-formula-in-fol)
  - [5.4. Automatic instantiation](#54-automatic-instantiation)
    - [Predicate with arity 2](#predicate-with-arity-2)
- [6. Installing system-wide (Linux systems)](#6-installing-system-wide-linux-systems)
- [7. Importante Notes](#7-importante-notes)
  - [7.1. Always use single quotes '...'](#71-always-use-single-quotes-)
  - [7.2. The Bash shell treats ! as history expansion](#72-the-bash-shell-treats--as-history-expansion)
  - [7.3. Do not omit parentheses unnecessarily (Please respect it!)](#73-do-not-omit-parentheses-unnecessarily-please-respect-it)
- [8. Suggested Test Cases](#8-suggested-test-cases)

# 1. Introduction
Implemented in Rust — with Full Step-by-Step Proof Output

This project implements the Semantic Tableaux Method for:

* Propositional Logic
* First-Order Logic (FOL) with:
  * Predicates
  * Terms (variables and constants)
  * Quantifiers (forall, exists)
  * Automatic fresh-constant generation (c1, c2, …)

The program takes a formula as input, builds two tableaux:

* T(φ) — to test satisfiability
* F(φ) — to test validity

and prints the entire proof tree, including every applied rule.

# 2. Installation

## 2.1. Install Rust

> [!WARNING]INFO
> Please visit the official Rust website, the information below is a brief.

Installing Rust is very simple on macOS and Linux.
Go to the official Rust website:

[Rust Website - Installation](https://rust-lang.org/tools/install/)

There, they simply ask you to run the following command in your terminal:
```
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```
Follow the on-screen instructions — the download will begin, and within a few seconds Rust will be installed for your user.

Close the terminal and open it again.

This ensures that your shell now knows where Rust is installed.

## 2.2. Clone the repository
```
git clone https://github.com/cthadeusantos/tableaux.git
cd tableaux
```

## 2.3. Build the optimized executable

```
cargo build --release
```

The binary will located in:
```
target/release/tableaux
```

# 3. Running the Program

## 3.1. Basic syntax
```
./target/release/tableaux 'FORMULA'
```
> [!WARNING]
> Always use single quotes '...', otherwise the shell may misinterpret characters (especially !).

Example:

```
./target/release/tableaux 'p | !q'
```

# 4. Language Syntax

The system supports:

## 4.1. Propositional Connectives

| Connective | Logical symbol | Syntax in program |
|---|---|---|
| Negation | ¬A | !A or ~A |
| Conjunction | A ∧ B | A & B or A /\ B |
| Disjunction | A → B | A -> B |
| Implication | A → B | A -> B |

Examples:
```
(p -> q) & p
p \/ q
!(p & !q)
```

## 4.2. Predicates and Terms (FOL)
 
Predicates:
```
P(x)
Q(a,b)
R(x,y,z)
S
```

Terms:

* Variables: x, y, z
* Constants: a, b, c1, c2, …

The tableaux engine will automatically create fresh constants when needed.

## 4.3. Quantifiers (FOL)

Use:

### 4.3.1. Universal quantifier:

```
forall x FORMULA
```

Meaning: ∀x FORMULA

Example:

```
forall x (P(x) -> Q(x))
```

### 4.3.2. Existential quantifier:
```
exists x FORMULA
```

Meaning: ∃x FORMULA

Example:
```
exists y P(y)
```

# 5. Usage Examples

## 5.1. Arguments

Suppose you have an argument with:
```
Premises: A, B, C
Conclusion: D
```
The argument is valid if and only if:
```
A ∧ B ∧ C ⊨ D
```

### How to Pass This to the Program

#### Using Implication (Recommended)

Translate the argument:
```
A, B, C ⊢ D
```

into the formula:
```
(A & B & C) -> D
```

Then run the program:
```
./target/release/tableaux '(A & B & C) -> D'
```



## 5.2. Propositional logic

Unsatisfiable formula:

```
(p -> q) & p & !q
```

Run:

```
./target/release/tableaux '(p -> q) & p & !q'
```

The tableau should close all branches.

## 5.3. Valid formula in FOL

```
forall x (P(x) -> P(x))
```

Run:

```
./target/release/tableaux 'forall x (P(x) -> P(x))'
```

Expected:

* T(φ) is satisfiable
* F(φ) is unsatisfiable → φ is valid

## 5.4. Automatic instantiation

```
forall x P(x) -> exists x P(x)
```

Run:

```
./target/release/tableaux 'forall x P(x) -> exists x P(x)'
```

### Predicate with arity 2

```
forall x exists y R(x,y) -> exists y forall x R(x,y)
```

Run:

```
./target/release/tableaux 'forall x exists y R(x,y) -> exists y forall x R(x,y)'
```

# 6. Installing system-wide (Linux systems)

To make the command available globally:

```
sudo cp target/release/tableaux /usr/local/bin/
```

Run:

```
tableaux 'forall x P(x)'
```

# 7. Importante Notes

## 7.1. Always use single quotes '...'

Correct

```
'forall x (P(x) -> Q(x))'
```

Incorrect:

```
"forall x (P(x) -> Q(x))"   # may break due to ! or shell parsing
```

## 7.2. The Bash shell treats ! as history expansion

Correct

```
'!p | q'
```

Incorrect:

```
!p | q       # ERROR
```
    
## 7.3. Do not omit parentheses unnecessarily (Please respect it!)

Parser accepts:

```
forall x (P(x) -> Q(x))
```

# 8. Suggested Test Cases
Valid:

```
forall x P(x) -> exists x P(x)
```

Not valid:

```
exists x P(x) -> forall x P(x)
```

Satisfiable but not valid:

```
exists x (P(x) & !Q(x))
```