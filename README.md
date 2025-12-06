# **Semantic Tableaux for Propositional and First-Order Logic** <!-- omit in toc -->

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

## 2.1. Clone the repository
```
git clone https://github.com/YOUR_USER/tableaux.git
cd tableaux
```

## 2.2. Build the optimized executable

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

## 5.1. Propositional logic

Unsatisfiable formula:

```
(p -> q) & p & !q
```

Run:

```
./target/release/tableaux '(p -> q) & p & !q'
```

The tableau should close all branches.

## 5.2. Valid formula in FOL

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

## 5.3. Automatic instantiation

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