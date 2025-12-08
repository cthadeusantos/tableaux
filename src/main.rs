//use std::collections::{HashMap, HashSet};
use std::collections::HashSet;
use std::env;
use std::io::{self, Read};

//
// ====== TOKENS ======
//

#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Ident(String),
    Not,
    And,
    Or,
    Imp,
    Iff,
    LPar,
    RPar,
    Comma,
    End,
}

//
// ====== TERMS & FORMULAS (FIRST-ORDER) ======
//

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Term {
    Var(String),
    Const(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Formula {
    Pred(String, Vec<Term>),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Imp(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    ForAll(String, Box<Formula>),
    Exists(String, Box<Formula>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Sign {
    T,
    F,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Signed {
    sign: Sign,
    formula: Formula,
}

impl Signed {
    fn new(sign: Sign, formula: Formula) -> Self {
        Signed { sign, formula }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct AtomKey {
    name: String,
    args: Vec<Term>,
}

//
// ====== PRETTY PRINT ======
//

fn pretty_term(t: &Term) -> String {
    match t {
        Term::Var(v) => v.clone(),
        Term::Const(c) => c.clone(),
    }
}

fn pretty_formula(f: &Formula) -> String {
    match f {
        Formula::Pred(name, args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let a: Vec<String> = args.iter().map(pretty_term).collect();
                format!("{}({})", name, a.join(", "))
            }
        }
        Formula::Not(a) => format!("¬{}", pretty_formula(a)),
        Formula::And(a, b) => format!("({} ∧ {})", pretty_formula(a), pretty_formula(b)),
        Formula::Or(a, b) => format!("({} ∨ {})", pretty_formula(a), pretty_formula(b)),
        Formula::Imp(a, b) => format!("({} → {})", pretty_formula(a), pretty_formula(b)),
        Formula::Iff(a, b) => format!("({} ↔ {})", pretty_formula(a), pretty_formula(b)),
        Formula::ForAll(v, body) => format!("∀{} {}", v, pretty_formula(body)),
        Formula::Exists(v, body) => format!("∃{} {}", v, pretty_formula(body)),
    }
}

fn pretty_signed(s: &Signed) -> String {
    let sig = match s.sign {
        Sign::T => "T",
        Sign::F => "F",
    };
    format!("{} {}", sig, pretty_formula(&s.formula))
}

fn pretty_atom(a: &AtomKey) -> String {
    if a.args.is_empty() {
        a.name.clone()
    } else {
        let a_s: Vec<String> = a.args.iter().map(pretty_term).collect();
        format!("{}({})", a.name, a_s.join(", "))
    }
}

//
// ====== LEXER ======
//

fn tokenize(s: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let chs: Vec<char> = s.chars().collect();
    let mut i = 0;
    let n = chs.len();

    while i < n {
        let c = chs[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }

        // <-> (iff)
        if i + 2 < n && chs[i] == '<' && chs[i + 1] == '-' && chs[i + 2] == '>' {
            tokens.push(Token::Iff);
            i += 3;
            continue;
        }

        // -> (imp)
        if i + 1 < n && chs[i] == '-' && chs[i + 1] == '>' {
            tokens.push(Token::Imp);
            i += 2;
            continue;
        }

        match c {
            '(' => { tokens.push(Token::LPar); i += 1; }
            ')' => { tokens.push(Token::RPar); i += 1; }
            ',' => { tokens.push(Token::Comma); i += 1; }
            '~' | '!' => { tokens.push(Token::Not); i += 1; }
            '&' | '∧' => { tokens.push(Token::And); i += 1; }
            '|' | '∨' | 'v' | 'V' => { tokens.push(Token::Or); i += 1; }
            '/' => {
                if i + 1 < n && chs[i + 1] == '\\' {
                    tokens.push(Token::And);
                    i += 2;
                } else {
                    i += 1;
                }
            }
            '\\' => {
                if i + 1 < n && chs[i + 1] == '/' {
                    tokens.push(Token::Or);
                    i += 2;
                } else {
                    i += 1;
                }
            }
            _ => {
                if c.is_alphanumeric() || c == '_' {
                    let mut j = i;
                    let mut ident = String::new();
                    while j < n && (chs[j].is_alphanumeric() || chs[j] == '_') {
                        ident.push(chs[j]);
                        j += 1;
                    }
                    tokens.push(Token::Ident(ident));
                    i = j;
                } else {
                    // ignora caracteres estranhos
                    i += 1;
                }
            }
        }
    }

    tokens.push(Token::End);
    tokens
}

//
// ====== PARSER ======
//

struct Parser {
    toks: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(toks: Vec<Token>) -> Self {
        Parser { toks, pos: 0 }
    }

    fn peek(&self) -> &Token {
        &self.toks[self.pos]
    }

    fn bump(&mut self) {
        if self.pos < self.toks.len() {
            self.pos += 1;
        }
    }

    fn eat(&mut self, expected: &Token) -> bool {
        if self.peek() == expected {
            self.bump();
            true
        } else {
            false
        }
    }

    fn parse(&mut self) -> Result<Formula, String> {
        self.parse_iff()
    }

    // Iff > Imp > Or > And > Unary
    fn parse_iff(&mut self) -> Result<Formula, String> {
        let mut left = self.parse_imp()?;
        while let Token::Iff = self.peek() {
            self.bump();
            let right = self.parse_imp()?;
            left = Formula::Iff(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_imp(&mut self) -> Result<Formula, String> {
        let left = self.parse_or()?;
        if let Token::Imp = self.peek() {
            self.bump();
            let right = self.parse_imp()?;
            Ok(Formula::Imp(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn parse_or(&mut self) -> Result<Formula, String> {
        let mut left = self.parse_and()?;
        loop {
            match self.peek() {
                Token::Or => {
                    self.bump();
                    let r = self.parse_and()?;
                    left = Formula::Or(Box::new(left), Box::new(r));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Formula, String> {
        let mut left = self.parse_unary()?;
        loop {
            match self.peek() {
                Token::And => {
                    self.bump();
                    let r = self.parse_unary()?;
                    left = Formula::And(Box::new(left), Box::new(r));
                }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Formula, String> {
        match self.peek() {
            Token::Not => {
                self.bump();
                let inner = self.parse_unary()?;
                Ok(Formula::Not(Box::new(inner)))
            }
            Token::LPar => {
                self.bump();
                let expr = self.parse()?;
                if !self.eat(&Token::RPar) {
                    return Err("Missing ')'".to_string());
                }
                Ok(expr)
            }
            Token::Ident(name) => {
                let kw = name.clone();
                if kw == "forall" || kw == "exists" {
                    // quantificador
                    self.bump(); // consume 'forall' / 'exists'
                    let var_name = match self.peek() {
                        Token::Ident(v) => v.clone(),
                        _ => return Err("Expected variable after 'forall'/'exists'".to_string()),
                    };
                    self.bump(); // consume var
                    // corpo do quantificador
                    let body = self.parse_unary()?;
                    if kw == "forall" {
                        Ok(Formula::ForAll(var_name, Box::new(body)))
                    } else {
                        Ok(Formula::Exists(var_name, Box::new(body)))
                    }
                } else {
                    self.parse_atomic()
                }
            }
            _ => Err(format!("Unexpected token: {:?}", self.peek())),
        }
    }

    fn parse_atomic(&mut self) -> Result<Formula, String> {
        let name = match self.peek() {
            Token::Ident(s) => s.clone(),
            _ => return Err("Expected predicate name".to_string()),
        };
        self.bump(); // consume name

        match self.peek() {
            Token::LPar => {
                self.bump(); // '('
                let mut args = Vec::new();
                if !matches!(self.peek(), Token::RPar) {
                    loop {
                        let t = self.parse_term()?;
                        args.push(t);
                        if let Token::Comma = self.peek() {
                            self.bump();
                            continue;
                        } else {
                            break;
                        }
                    }
                }
                if !self.eat(&Token::RPar) {
                    return Err("Expected ')' after argument list".to_string());
                }
                Ok(Formula::Pred(name, args))
            }
            _ => Ok(Formula::Pred(name, vec![])), // propositional atom
        }
    }

    fn parse_term(&mut self) -> Result<Term, String> {
        match self.peek() {
            Token::Ident(s) => {
                let n = s.clone();
                self.bump();
                Ok(Term::Var(n))
            }
            _ => Err("Expected term (identifier)".to_string()),
        }
    }
}

//
// ====== SUBSTITUIÇÃO (para quantificadores) ======
//

fn subst_term(term: &Term, var: &str, repl: &Term) -> Term {
    match term {
        Term::Var(v) if v == var => repl.clone(),
        _ => term.clone(),
    }
}

fn subst_formula(formula: &Formula, var: &str, repl: &Term) -> Formula {
    use Formula::*;
    match formula {
        Pred(name, args) => {
            let new_args: Vec<Term> = args.iter().map(|t| subst_term(t, var, repl)).collect();
            Pred(name.clone(), new_args)
        }
        Not(a) => Not(Box::new(subst_formula(a, var, repl))),
        And(a, b) => And(
            Box::new(subst_formula(a, var, repl)),
            Box::new(subst_formula(b, var, repl)),
        ),
        Or(a, b) => Or(
            Box::new(subst_formula(a, var, repl)),
            Box::new(subst_formula(b, var, repl)),
        ),
        Imp(a, b) => Imp(
            Box::new(subst_formula(a, var, repl)),
            Box::new(subst_formula(b, var, repl)),
        ),
        Iff(a, b) => Iff(
            Box::new(subst_formula(a, var, repl)),
            Box::new(subst_formula(b, var, repl)),
        ),
        ForAll(bound, body) => {
            if bound == var {
                ForAll(bound.clone(), body.clone())
            } else {
                ForAll(bound.clone(), Box::new(subst_formula(body, var, repl)))
            }
        }
        Exists(bound, body) => {
            if bound == var {
                Exists(bound.clone(), body.clone())
            } else {
                Exists(bound.clone(), Box::new(subst_formula(body, var, repl)))
            }
        }
    }
}

//
// ====== ÁTOMOS, CONTRADIÇÃO ======
//

fn atom_from_signed(s: &Signed) -> Option<(bool, AtomKey)> {
    match &s.formula {
        Formula::Pred(name, args) => {
            let key = AtomKey { name: name.clone(), args: args.clone() };
            match s.sign {
                Sign::T => Some((true, key)),
                Sign::F => Some((false, key)),
            }
        }
        Formula::Not(inner) => {
            if let Formula::Pred(name, args) = &**inner {
                let key = AtomKey { name: name.clone(), args: args.clone() };
                match s.sign {
                    Sign::T => Some((false, key)), // T ¬P
                    Sign::F => Some((true, key)),  // F ¬P
                }
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_literal(s: &Signed) -> bool {
    match &s.formula {
        Formula::Pred(_, _) => true,
        Formula::Not(inner) => matches!(&**inner, Formula::Pred(_, _)),
        _ => false,
    }
}

fn find_contradiction(formulas: &[Signed]) -> Option<AtomKey> {
    let mut tset = HashSet::new();
    let mut fset = HashSet::new();
    for s in formulas {
        if let Some((val, atom)) = atom_from_signed(s) {
            if val { tset.insert(atom.clone()); } else { fset.insert(atom.clone()); }
        }
    }
    for a in tset.iter() {
        if fset.contains(a) {
            return Some(a.clone());
        }
    }
    None
}

// fn is_closed_branch(formulas: &[Signed]) -> bool {
//     find_contradiction(formulas).is_some()
// }

//
// ====== CONSTANTES NO RAMO ======
//

fn collect_consts_in_formula(f: &Formula, acc: &mut HashSet<String>) {
    match f {
        Formula::Pred(_, args) => {
            for t in args {
                if let Term::Const(c) = t {
                    acc.insert(c.clone());
                }
            }
        }
        Formula::Not(a)
        | Formula::ForAll(_, a)
        | Formula::Exists(_, a) => collect_consts_in_formula(a, acc),
        Formula::And(a, b)
        | Formula::Or(a, b)
        | Formula::Imp(a, b)
        | Formula::Iff(a, b) => {
            collect_consts_in_formula(a, acc);
            collect_consts_in_formula(b, acc);
        }
    }
}

fn constants_in_branch(formulas: &[Signed]) -> HashSet<String> {
    let mut acc = HashSet::new();
    for s in formulas {
        collect_consts_in_formula(&s.formula, &mut acc);
    }
    acc
}

//
// ====== CONTEXTO (fresh constants) ======
//

struct TableauContext {
    next_const_id: usize,
}

impl TableauContext {
    fn new() -> Self {
        TableauContext { next_const_id: 1 }
    }

    fn fresh_const(&mut self) -> String {
        let c = format!("c{}", self.next_const_id);
        self.next_const_id += 1;
        c
    }
}

//
// ====== EXPANSÃO ======
//

enum Expansion {
    Add(Vec<Signed>),
    Branch(Vec<Signed>, Vec<Signed>),
    None,
}

fn expand_signed(s: &Signed, formulas: &[Signed], ctx: &mut TableauContext) -> (Expansion, String) {
    use Formula::*;
    use Sign::*;

    match (&s.sign, &s.formula) {
        (T, And(a, b)) => (
            Expansion::Add(vec![
                Signed::new(T, (*a.clone()).clone()),
                Signed::new(T, (*b.clone()).clone()),
            ]),
            "T-∧: T(A∧B) ⇒ T A, T B".to_string(),
        ),
        (F, Or(a, b)) => (
            Expansion::Add(vec![
                Signed::new(F, (*a.clone()).clone()),
                Signed::new(F, (*b.clone()).clone()),
            ]),
            "F-∨: F(A∨B) ⇒ F A, F B".to_string(),
        ),
        (T, Or(a, b)) => (
            Expansion::Branch(
                vec![Signed::new(T, (*a.clone()).clone())],
                vec![Signed::new(T, (*b.clone()).clone())],
            ),
            "T-∨: T(A∨B) ⇒ ramifica em T A | T B".to_string(),
        ),
        (F, And(a, b)) => (
            Expansion::Branch(
                vec![Signed::new(F, (*a.clone()).clone())],
                vec![Signed::new(F, (*b.clone()).clone())],
            ),
            "F-∧: F(A∧B) ⇒ ramifica em F A | F B".to_string(),
        ),
        (T, Imp(a, b)) => (
            Expansion::Branch(
                vec![Signed::new(F, (*a.clone()).clone())],
                vec![Signed::new(T, (*b.clone()).clone())],
            ),
            "T-→: T(A→B) ⇒ ramifica em F A | T B".to_string(),
        ),
        (F, Imp(a, b)) => (
            Expansion::Add(vec![
                Signed::new(T, (*a.clone()).clone()),
                Signed::new(F, (*b.clone()).clone()),
            ]),
            "F-→: F(A→B) ⇒ T A, F B".to_string(),
        ),
        (T, Not(a)) => (
            Expansion::Add(vec![Signed::new(F, (*a.clone()).clone())]),
            "T-¬: T¬A ⇒ F A".to_string(),
        ),
        (F, Not(a)) => (
            Expansion::Add(vec![Signed::new(T, (*a.clone()).clone())]),
            "F-¬: F¬A ⇒ T A".to_string(),
        ),
        (T, Iff(a, b)) => (
            Expansion::Branch(
                vec![Signed::new(T, (*a.clone()).clone()), Signed::new(T, (*b.clone()).clone())],
                vec![Signed::new(F, (*a.clone()).clone()), Signed::new(F, (*b.clone()).clone())],
            ),
            "T-↔: T(A↔B) ⇒ (T A, T B) | (F A, F B)".to_string(),
        ),
        (F, Iff(a, b)) => (
            Expansion::Branch(
                vec![Signed::new(T, (*a.clone()).clone()), Signed::new(F, (*b.clone()).clone())],
                vec![Signed::new(F, (*a.clone()).clone()), Signed::new(T, (*b.clone()).clone())],
            ),
            "F-↔: F(A↔B) ⇒ (T A, F B) | (F A, T B)".to_string(),
        ),

        // Quantifiers

        // γ: T ∀x φ(x)
        (T, ForAll(v, body)) => {
            let consts = constants_in_branch(formulas);
            let mut new_f = Vec::new();
            if consts.is_empty() {
                let cname = ctx.fresh_const();
                let t = Term::Const(cname);
                let inst = subst_formula(body, v, &t);
                new_f.push(Signed::new(T, inst));
            } else {
                for c in consts {
                    let t = Term::Const(c);
                    let inst = subst_formula(body, v, &t);
                    new_f.push(Signed::new(T, inst));
                }
            }
            (
                Expansion::Add(new_f),
                "T-∀ (γ): T(∀x φ(x)) ⇒ T φ(c) para constantes do ramo".to_string(),
            )
        }

        // γ: F ∃x φ(x)
        (F, Exists(v, body)) => {
            let consts = constants_in_branch(formulas);
            let mut new_f = Vec::new();
            if consts.is_empty() {
                let cname = ctx.fresh_const();
                let t = Term::Const(cname);
                let inst = subst_formula(body, v, &t);
                new_f.push(Signed::new(F, inst));
            } else {
                for c in consts {
                    let t = Term::Const(c);
                    let inst = subst_formula(body, v, &t);
                    new_f.push(Signed::new(F, inst));
                }
            }
            (
                Expansion::Add(new_f),
                "F-∃ (γ): F(∃x φ(x)) ⇒ F φ(c) para constantes do ramo".to_string(),
            )
        }

        // δ: F ∀x φ(x)
        (F, ForAll(v, body)) => {
            let cname = ctx.fresh_const();
            let t = Term::Const(cname);
            let inst = subst_formula(body, v, &t);
            (
                Expansion::Add(vec![Signed::new(F, inst)]),
                "F-∀ (δ): F(∀x φ(x)) ⇒ F φ(c) com c nova".to_string(),
            )
        }

        // δ: T ∃x φ(x)
        (T, Exists(v, body)) => {
            let cname = ctx.fresh_const();
            let t = Term::Const(cname);
            let inst = subst_formula(body, v, &t);
            (
                Expansion::Add(vec![Signed::new(T, inst)]),
                "T-∃ (δ): T(∃x φ(x)) ⇒ T φ(c) com c nova".to_string(),
            )
        }

        _ => (Expansion::None, "Nenhuma regra aplicável (literal ou caso não tratado)".to_string()),
    }
}

//
// ====== TABLEAUX (versão simples, DFS) ======
//

fn expand_branch(
    mut formulas: Vec<Signed>,
    mut applied: HashSet<Signed>,
    depth: usize,
    ctx: &mut TableauContext,
) -> bool {
    let pad = " ".repeat(depth * 2);

    // Checa fechamento
    if let Some(atom) = find_contradiction(&formulas) {
        println!("{}Folha FECHADA (contradição em {}).", pad, pretty_atom(&atom));
        let lits: Vec<String> = formulas.iter().map(pretty_signed).collect();
        println!("{}  Ramo: {}", pad, lits.join(", "));
        return false;
    }

    // Escolhe fórmula não literal não aplicada
    let mut target: Option<Signed> = None;
    for s in &formulas {
        if !is_literal(s) && !applied.contains(s) {
            target = Some(s.clone());
            break;
        }
    }

    let s = match target {
        None => {
            // ramo aberto
            println!("{}Folha ABERTA (nenhuma regra mais aplicável).", pad);
            let lits: Vec<String> = formulas.iter().map(pretty_signed).collect();
            println!("{}  Ramo: {}", pad, lits.join(", "));
            return true; // existe ramo aberto
        }
        Some(sf) => sf,
    };

    applied.insert(s.clone());
    let (expansion, rule_name) = expand_signed(&s, &formulas, ctx);

    match expansion {
        Expansion::None => {
            println!("{}[INFO] Nenhuma regra para {}", pad, pretty_signed(&s));
            expand_branch(formulas, applied, depth, ctx)
        }
        Expansion::Add(new_fs) => {
            let added: Vec<String> = new_fs.iter().map(pretty_signed).collect();
            println!("{}Expande: {}  usando: {}", pad, pretty_signed(&s), rule_name);
            println!("{}  ⇒ Adiciona: {}", pad, added.join(", "));
            for nf in new_fs {
                if !formulas.contains(&nf) {
                    formulas.push(nf);
                }
            }
            expand_branch(formulas, applied, depth + 1, ctx)
        }
        Expansion::Branch(left_add, right_add) => {
            let left_s: Vec<String> = left_add.iter().map(pretty_signed).collect();
            let right_s: Vec<String> = right_add.iter().map(pretty_signed).collect();
            println!("{}Expande (ramificação): {}  usando: {}", pad, pretty_signed(&s), rule_name);
            println!("{}  ⇒ Ramo 1 adiciona: {}", pad, left_s.join(", "));
            println!("{}  ⇒ Ramo 2 adiciona: {}", pad, right_s.join(", "));

            let mut left_formulas = formulas.clone();
            let mut left_applied = applied.clone();
            for nf in left_add {
                if !left_formulas.contains(&nf) {
                    left_formulas.push(nf);
                }
            }

            let mut right_formulas = formulas;
            let mut right_applied = applied;
            for nf in right_add {
                if !right_formulas.contains(&nf) {
                    right_formulas.push(nf);
                }
            }

            println!("{}[Ramo 1]", pad);
            let open_left = expand_branch(left_formulas, left_applied, depth + 1, ctx);
            println!("{}[Ramo 2]", pad);
            let open_right = expand_branch(right_formulas, right_applied, depth + 1, ctx);

            open_left || open_right
        }
    }
}

//
// ====== MAIN ======
//

fn main() {
    let args: Vec<String> = env::args().collect();
    let formula_str = if args.len() > 1 {
        args[1..].join(" ")
    } else {
        println!("Digite a fórmula (ex.: forall x (P(x) -> exists x P(x))):");
        let mut s = String::new();
        io::stdin().read_to_string(&mut s).expect("erro lendo stdin");
        s
    };

    let toks = tokenize(&formula_str);
    let mut parser = Parser::new(toks);
    let phi = match parser.parse() {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Erro no parser: {}", e);
            return;
        }
    };

    println!("Fórmula: {}", pretty_formula(&phi));
    println!();

    // T(φ) – satisfatibilidade
    println!("=== TABLEAU para T(φ) — satisfatibilidade ===");
    let mut ctx1 = TableauContext::new();
    let sat = expand_branch(vec![Signed::new(Sign::T, phi.clone())], HashSet::new(), 0, &mut ctx1);
    if sat {
        println!("Resultado: existe ramo aberto → φ é SATISFATÍVEL.");
    } else {
        println!("Resultado: todos os ramos fecham → φ é INSATISFATÍVEL.");
    }

    println!();

    // F(φ) – validade
    println!("=== TABLEAU para F(φ) — validade ===");
    let mut ctx2 = TableauContext::new();
    let sat_f = expand_branch(vec![Signed::new(Sign::F, phi.clone())], HashSet::new(), 0, &mut ctx2);
    if sat_f {
        println!("Resultado: existe ramo aberto → F(φ) é SATISFATÍVEL → φ NÃO é válida.");
    } else {
        println!("Resultado: todos os ramos fecham → F(φ) é INSATISFATÍVEL → φ É VÁLIDA.");
    }
}
