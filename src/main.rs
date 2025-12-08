use std::collections::{HashMap, HashSet};
use std::env;
use std::io::{self, Read};

// =========================
// Léxico
// =========================

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

// =========================
// Termos e Fórmulas (LPO)
// =========================

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
    ForAll(String, Box<Formula>),  // ∀x φ
    Exists(String, Box<Formula>),  // ∃x φ
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

// Para identificar átomos em modelos / contradições
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct AtomKey {
    name: String,
    args: Vec<Term>,
}

// =========================
// Impressão bonitinha
// =========================

fn pretty_print_term(t: &Term) -> String {
    match t {
        Term::Var(v) => v.clone(),
        Term::Const(c) => c.clone(),
    }
}

fn pretty_print_formula(f: &Formula) -> String {
    match f {
        Formula::Pred(name, args) => {
            if args.is_empty() {
                name.clone()
            } else {
                let parts: Vec<String> = args.iter().map(|t| pretty_print_term(t)).collect();
                format!("{}({})", name, parts.join(", "))
            }
        }
        Formula::Not(a) => format!("¬{}", pretty_print_formula(a)),
        Formula::And(a, b) => format!("({} ∧ {})", pretty_print_formula(a), pretty_print_formula(b)),
        Formula::Or(a, b) => format!("({} ∨ {})", pretty_print_formula(a), pretty_print_formula(b)),
        Formula::Imp(a, b) => format!("({} → {})", pretty_print_formula(a), pretty_print_formula(b)),
        Formula::Iff(a, b) => format!("({} ↔ {})", pretty_print_formula(a), pretty_print_formula(b)),
        Formula::ForAll(v, body) => format!("∀{} {}", v, pretty_print_formula(body)),
        Formula::Exists(v, body) => format!("∃{} {}", v, pretty_print_formula(body)),
    }
}

fn pretty_print_signed(s: &Signed) -> String {
    let sign_str = match s.sign {
        Sign::T => "T",
        Sign::F => "F",
    };
    format!("{} {}", sign_str, pretty_print_formula(&s.formula))
}

fn pretty_print_atom(a: &AtomKey) -> String {
    if a.args.is_empty() {
        a.name.clone()
    } else {
        let parts: Vec<String> = a.args.iter().map(|t| pretty_print_term(t)).collect();
        format!("{}({})", a.name, parts.join(", "))
    }
}

// =========================
// Lexer
// =========================

fn tokenize(s: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut i = 0;
    let chs: Vec<char> = s.chars().collect();
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
            '|' | 'v' | 'V' | '∨' => { tokens.push(Token::Or); i += 1; }
            '/' => {
                if i + 1 < n && chs[i + 1] == '\\' {
                    tokens.push(Token::And);
                    i += 2;
                } else { i += 1; }
            }
            '\\' => {
                if i + 1 < n && chs[i + 1] == '/' {
                    tokens.push(Token::Or);
                    i += 2;
                } else { i += 1; }
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
                    // caractere desconhecido, ignora
                    i += 1;
                }
            }
        }
    }

    tokens.push(Token::End);
    tokens
}

// =========================
// Parser
// =========================

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

    // Precedência: Iff > Imp > Or > And > Unary
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
                    return Err("Parênteses não fechados".to_string());
                }
                Ok(expr)
            }
            Token::Ident(name) => {
                let kw = name.clone();
                if kw == "forall" || kw == "exists" {
                    self.bump(); // come 'forall' ou 'exists'
                    let var_name = match self.peek() {
                        Token::Ident(v) => v.clone(),
                        _ => return Err("Esperado identificador de variável após 'forall'/'exists'".to_string()),
                    };
                    self.bump(); // come a variável
                    // Corpo do quantificador: parse_unary() para pegar algo como (P(x) -> Q(x))
                    let body = self.parse_unary()?;
                    if kw == "forall" {
                        Ok(Formula::ForAll(var_name, Box::new(body)))
                    } else {
                        Ok(Formula::Exists(var_name, Box::new(body)))
                    }
                } else {
                    // Predicado/átomo
                    self.parse_atomic()
                }
            }
            _ => Err(format!("Token inesperado: {:?}", self.peek())),
        }
    }

    fn parse_atomic(&mut self) -> Result<Formula, String> {
        let name = match self.peek() {
            Token::Ident(s) => s.clone(),
            _ => return Err("Esperado identificador de predicado".to_string()),
        };
        self.bump(); // consome o nome

        match self.peek() {
            Token::LPar => {
                // predicado com argumentos: P(t1, t2, ...)
                self.bump(); // '('
                let mut args = Vec::new();
                if !matches!(self.peek(), Token::RPar) {
                    loop {
                        let term = self.parse_term()?;
                        args.push(term);
                        if let Token::Comma = self.peek() {
                            self.bump();
                            continue;
                        } else {
                            break;
                        }
                    }
                }
                if !self.eat(&Token::RPar) {
                    return Err("Esperado ')' após lista de termos".to_string());
                }
                Ok(Formula::Pred(name, args))
            }
            _ => {
                // predicado 0-ário (tipo proposição simples)
                Ok(Formula::Pred(name, vec![]))
            }
        }
    }

    fn parse_term(&mut self) -> Result<Term, String> {
        match self.peek() {
            Token::Ident(s) => {
                let n = s.clone();
                self.bump();
                // por simplicidade, tratamos identificadores da entrada como variáveis;
                // as constantes "c1", "c2"... são geradas internamente.
                Ok(Term::Var(n))
            }
            _ => Err("Esperado termo (identificador)".to_string()),
        }
    }
}

// =========================
// Substituição (para quantificadores)
// =========================

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
                ForAll(bound.clone(), body.clone()) // var está ligada aqui, não substitui
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

// =========================
// Auxílio para átomos / contradições / modelo
// =========================

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
                    Sign::T => Some((false, key)), // T ¬P => P é falso
                    Sign::F => Some((true, key)),  // F ¬P => P é verdadeiro
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

// =========================
// Ramo do Tableau
// =========================

#[derive(Debug, Clone)]
struct TableauBranch {
    formulas: Vec<Signed>,
    applied: HashSet<Signed>, // fórmulas já expandidas
}

impl TableauBranch {
    fn new(initial: Vec<Signed>) -> Self {
        TableauBranch { formulas: initial, applied: HashSet::new() }
    }

    fn is_closed(&self) -> bool {
        self.find_contradiction_atom().is_some()
    }

    fn find_contradiction_atom(&self) -> Option<AtomKey> {
        let mut tset: HashSet<AtomKey> = HashSet::new();
        let mut fset: HashSet<AtomKey> = HashSet::new();
        for s in &self.formulas {
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
}

// coletar constantes presentes no ramo (para γ de ∀ e ∃)
fn collect_consts_in_formula(formula: &Formula, acc: &mut HashSet<String>) {
    match formula {
        Formula::Pred(_, args) => {
            for t in args {
                if let Term::Const(c) = t {
                    acc.insert(c.clone());
                }
            }
        }
        Formula::Not(a) |
        Formula::ForAll(_, a) |
        Formula::Exists(_, a) => collect_consts_in_formula(a, acc),
        Formula::And(a,b) |
        Formula::Or(a,b) |
        Formula::Imp(a,b) |
        Formula::Iff(a,b) => {
            collect_consts_in_formula(a, acc);
            collect_consts_in_formula(b, acc);
        }
    }
}

fn constants_in_branch(br: &TableauBranch) -> HashSet<String> {
    let mut acc = HashSet::new();
    for s in &br.formulas {
        collect_consts_in_formula(&s.formula, &mut acc);
    }
    acc
}

// =========================
// Geração de constantes frescas
// =========================

struct TableauContext {
    next_const_id: usize,
}

impl TableauContext {
    fn new() -> Self {
        TableauContext { next_const_id: 1 }
    }

    fn fresh_const(&mut self) -> String {
        let name = format!("c{}", self.next_const_id);
        self.next_const_id += 1;
        name
    }
}

// =========================
// Regras de expansão (α, β, γ, δ)
// =========================

enum Expansion {
    Add(Vec<Signed>),
    Branch(Vec<Signed>, Vec<Signed>),
    None,
}

// escolhe uma fórmula não literal não expandida
fn choose_unexpanded(branch: &TableauBranch) -> Option<Signed> {
    for s in &branch.formulas {
        if is_literal(s) {
            continue;
        }
        if !branch.applied.contains(s) {
            return Some(s.clone());
        }
    }
    None
}

fn signed_set_contains(set: &Vec<Signed>, s: &Signed) -> bool {
    set.iter().any(|x| x == s)
}

fn add_unique(target: &mut Vec<Signed>, new: Vec<Signed>) {
    for s in new {
        if !signed_set_contains(target, &s) {
            target.push(s);
        }
    }
}

fn expand_signed(signed: &Signed, branch: &TableauBranch, ctx: &mut TableauContext) -> (Expansion, String) {
    use Formula::*;
    use Sign::*;

    match (&signed.sign, &signed.formula) {
        // proposicionais (como antes)
        (T, And(a,b)) => (
            Expansion::Add(vec![
                Signed::new(T, (*a.clone()).clone()),
                Signed::new(T, (*b.clone()).clone()),
            ]),
            "Regra T-∧ (α): T(A∧B) ⇒ T A, T B".to_string(),
        ),
        (F, Or(a,b)) => (
            Expansion::Add(vec![
                Signed::new(F, (*a.clone()).clone()),
                Signed::new(F, (*b.clone()).clone()),
            ]),
            "Regra F-∨ (α): F(A∨B) ⇒ F A, F B".to_string(),
        ),
        (T, Or(a,b)) => (
            Expansion::Branch(
                vec![Signed::new(T, (*a.clone()).clone())],
                vec![Signed::new(T, (*b.clone()).clone())],
            ),
            "Regra T-∨ (β): T(A∨B) ⇒ ramo T A | ramo T B".to_string(),
        ),
        (F, And(a,b)) => (
            Expansion::Branch(
                vec![Signed::new(F, (*a.clone()).clone())],
                vec![Signed::new(F, (*b.clone()).clone())],
            ),
            "Regra F-∧ (β): F(A∧B) ⇒ ramo F A | ramo F B".to_string(),
        ),
        (T, Imp(a,b)) => (
            Expansion::Branch(
                vec![Signed::new(F, (*a.clone()).clone())],
                vec![Signed::new(T, (*b.clone()).clone())],
            ),
            "Regra T-→ (β): T(A→B) ⇒ ramo F A | ramo T B".to_string(),
        ),
        (F, Imp(a,b)) => (
            Expansion::Add(vec![
                Signed::new(T, (*a.clone()).clone()),
                Signed::new(F, (*b.clone()).clone()),
            ]),
            "Regra F-→ (α): F(A→B) ⇒ T A, F B".to_string(),
        ),
        (T, Not(a)) => (
            Expansion::Add(vec![Signed::new(F, (*a.clone()).clone())]),
            "Regra T-¬: T¬A ⇒ F A".to_string(),
        ),
        (F, Not(a)) => (
            Expansion::Add(vec![Signed::new(T, (*a.clone()).clone())]),
            "Regra F-¬: F¬A ⇒ T A".to_string(),
        ),
        (T, Iff(a,b)) => (
            Expansion::Branch(
                vec![Signed::new(T, (*a.clone()).clone()), Signed::new(T, (*b.clone()).clone())],
                vec![Signed::new(F, (*a.clone()).clone()), Signed::new(F, (*b.clone()).clone())],
            ),
            "Regra T-↔ (β): T(A↔B) ⇒ ramo (T A, T B) | ramo (F A, F B)".to_string(),
        ),
        (F, Iff(a,b)) => (
            Expansion::Branch(
                vec![Signed::new(T, (*a.clone()).clone()), Signed::new(F, (*b.clone()).clone())],
                vec![Signed::new(F, (*a.clone()).clone()), Signed::new(T, (*b.clone()).clone())],
            ),
            "Regra F-↔ (β): F(A↔B) ⇒ ramo (T A, F B) | ramo (F A, T B)".to_string(),
        ),

        // Quantificadores - γ e δ

        // γ: T ∀x φ(x)  — instancia com todas constantes do ramo; se não houver, cria uma.
        (T, ForAll(v, body)) => {
            let consts = constants_in_branch(branch);
            let mut new_formulas = Vec::new();
            if consts.is_empty() {
                let cname = ctx.fresh_const();
                let t = Term::Const(cname);
                let inst = subst_formula(body, v, &t);
                new_formulas.push(Signed::new(T, inst));
            } else {
                for c in consts {
                    let t = Term::Const(c);
                    let inst = subst_formula(body, v, &t);
                    new_formulas.push(Signed::new(T, inst));
                }
            }
            (
                Expansion::Add(new_formulas),
                "Regra T-∀ (γ): T(∀x φ(x)) ⇒ T φ(c) para constantes do ramo".to_string(),
            )
        }

        // γ: F ∃x φ(x)
        (F, Exists(v, body)) => {
            let consts = constants_in_branch(branch);
            let mut new_formulas = Vec::new();
            if consts.is_empty() {
                let cname = ctx.fresh_const();
                let t = Term::Const(cname);
                let inst = subst_formula(body, v, &t);
                new_formulas.push(Signed::new(F, inst));
            } else {
                for c in consts {
                    let t = Term::Const(c);
                    let inst = subst_formula(body, v, &t);
                    new_formulas.push(Signed::new(F, inst));
                }
            }
            (
                Expansion::Add(new_formulas),
                "Regra F-∃ (γ): F(∃x φ(x)) ⇒ F φ(c) para constantes do ramo".to_string(),
            )
        }

        // δ: F ∀x φ(x) — introduz nova constante c
        (F, ForAll(v, body)) => {
            let cname = ctx.fresh_const();
            let t = Term::Const(cname);
            let inst = subst_formula(body, v, &t);
            (
                Expansion::Add(vec![Signed::new(F, inst)]),
                "Regra F-∀ (δ): F(∀x φ(x)) ⇒ F φ(c) com c nova".to_string(),
            )
        }

        // δ: T ∃x φ(x) — introduz nova constante c
        (T, Exists(v, body)) => {
            let cname = ctx.fresh_const();
            let t = Term::Const(cname);
            let inst = subst_formula(body, v, &t);
            (
                Expansion::Add(vec![Signed::new(T, inst)]),
                "Regra T-∃ (δ): T(∃x φ(x)) ⇒ T φ(c) com c nova".to_string(),
            )
        }

        _ => (Expansion::None, "Sem regra aplicável (literal ou caso não tratado)".to_string()),
    }
}

// =========================
// Nó de prova (para saída passo a passo)
// =========================

#[derive(Clone, Debug)]
struct ProofNode {
    formulas: Vec<Signed>,
    expanded: Option<Signed>,
    rule: Option<String>,
    additions: Vec<Vec<Signed>>, // para Add: 1 vetor; para Branch: 2 vetores
    children: Vec<ProofNode>,
    closed: bool,
    model: Option<HashMap<AtomKey, bool>>,
}

fn build_model_from_formulas(formulas: &Vec<Signed>) -> Option<HashMap<AtomKey, bool>> {
    let mut model: HashMap<AtomKey, bool> = HashMap::new();
    for s in formulas {
        if let Some((val, atom)) = atom_from_signed(s) {
            model.insert(atom, val);
        }
    }
    Some(model)
}

fn detect_contradiction_atom_from_formulas(formulas: &Vec<Signed>) -> Option<AtomKey> {
    let mut tset: HashSet<AtomKey> = HashSet::new();
    let mut fset: HashSet<AtomKey> = HashSet::new();
    for s in formulas {
        if let Some((val, atom)) = atom_from_signed(s) {
            if val {
                tset.insert(atom.clone());
            } else {
                fset.insert(atom.clone());
            }
        }
    }
    for a in tset.iter() {
        if fset.contains(a) {
            return Some(a.clone());
        }
    }
    None
}

// Expande recursivamente um ramo, construindo a árvore de prova
fn expand_branch(mut br: TableauBranch, ctx: &mut TableauContext) -> ProofNode {
    if br.is_closed() {
        return ProofNode {
            formulas: br.formulas.clone(),
            expanded: None,
            rule: None,
            additions: vec![],
            children: vec![],
            closed: true,
            model: None,
        };
    }

    if let Some(s) = choose_unexpanded(&br) {
        br.applied.insert(s.clone());
        let (expansion, rule_name) = expand_signed(&s, &br, ctx);
        match expansion {
            Expansion::None => {
                // nada a fazer, tenta seguir
                expand_branch(br, ctx)
            }
            Expansion::Add(to_add) => {
                let mut new_br = br.clone();
                add_unique(&mut new_br.formulas, to_add.clone());
                let child = expand_branch(new_br, ctx);
                ProofNode {
                    formulas: br.formulas.clone(),
                    expanded: Some(s),
                    rule: Some(rule_name),
                    additions: vec![to_add],
                    children: vec![child.clone()],
                    closed: child.closed,
                    model: if !child.closed { child.model.clone() } else { None },
                }
            }
            Expansion::Branch(left_add, right_add) => {
                let mut left_br = br.clone();
                add_unique(&mut left_br.formulas, left_add.clone());
                let left_node = expand_branch(left_br, ctx);

                let mut right_br = br.clone();
                add_unique(&mut right_br.formulas, right_add.clone());
                let right_node = expand_branch(right_br, ctx);

                let closed_all = left_node.closed && right_node.closed;
                let chosen_model = if !left_node.closed {
                    left_node.model.clone()
                } else if !right_node.closed {
                    right_node.model.clone()
                } else {
                    None
                };

                ProofNode {
                    formulas: br.formulas.clone(),
                    expanded: Some(s),
                    rule: Some(rule_name),
                    additions: vec![left_add, right_add],
                    children: vec![left_node, right_node],
                    closed: closed_all,
                    model: chosen_model,
                }
            }
        }
    } else {
        // ramo saturado (sem fórmulas não literais não expandidas)
        let closed = br.is_closed();
        let model = if !closed {
            build_model_from_formulas(&br.formulas)
        } else {
            None
        };
        ProofNode {
            formulas: br.formulas.clone(),
            expanded: None,
            rule: None,
            additions: vec![],
            children: vec![],
            closed,
            model,
        }
    }
}

// Impressão recursiva da prova
fn print_proof_node(node: &ProofNode, indent: usize, label: &str) {
    let pad = " ".repeat(indent);

    if let Some(expanded) = &node.expanded {
        println!(
            "{}{} - Expande: {}. Regra: {}",
            pad,
            label,
            pretty_print_signed(expanded),
            node.rule.as_ref().unwrap()
        );
        if node.additions.len() == 1 {
            let added = &node.additions[0];
            let strs: Vec<String> = added.iter().map(|s| pretty_print_signed(s)).collect();
            println!("{}  ⇒ Adiciona: {}", pad, strs.join(", "));
            if !node.children.is_empty() {
                print_proof_node(&node.children[0], indent + 4, &format!("{}·1", label));
            }
        } else if node.additions.len() == 2 {
            let added_left: Vec<String> = node.additions[0].iter().map(|s| pretty_print_signed(s)).collect();
            let added_right: Vec<String> = node.additions[1].iter().map(|s| pretty_print_signed(s)).collect();
            println!("{}  ⇒ Cria dois ramos:", pad);
            println!("{}    Ramo 1 adiciona: {}", pad, added_left.join(", "));
            println!("{}    Ramo 2 adiciona: {}", pad, added_right.join(", "));
            if node.children.len() >= 1 {
                print_proof_node(&node.children[0], indent + 4, &format!("{}·1", label));
            }
            if node.children.len() >= 2 {
                print_proof_node(&node.children[1], indent + 4, &format!("{}·2", label));
            }
        }
    } else {
        if node.closed {
            if let Some(atom) = detect_contradiction_atom_from_formulas(&node.formulas) {
                println!(
                    "{}{} - Folha: Fechada (contradição em {}).",
                    pad,
                    label,
                    pretty_print_atom(&atom)
                );
            } else {
                println!("{}{} - Folha: Fechada (contradição).", pad, label);
            }
            let lits: Vec<String> = node.formulas.iter().map(|s| pretty_print_signed(s)).collect();
            println!("{}  Fórmulas no ramo: {}", pad, lits.join(", "));
        } else {
            println!("{}{} - Folha: Aberta (modelo parcial encontrado).", pad, label);
            if let Some(m) = &node.model {
                for (atom, val) in m {
                    println!("{}  {} = {}", pad, pretty_print_atom(atom), val);
                }
            }
            let lits: Vec<String> = node.formulas.iter().map(|s| pretty_print_signed(s)).collect();
            println!("{}  Fórmulas no ramo: {}", pad, lits.join(", "));
        }
    }
}

// =========================
// main
// =========================

fn main() {
    let args: Vec<String> = env::args().collect();
    let formula_str = if args.len() > 1 {
        args[1..].join(" ")
    } else {
        println!("Digite a fórmula (ex.: forall x (P(x) -> Q(x))):");
        let mut s = String::new();
        io::stdin().read_to_string(&mut s).expect("erro lendo stdin");
        s
    };

    let toks = tokenize(&formula_str);
    let mut parser = Parser::new(toks);
    let parsed = parser.parse();
    let phi = match parsed {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Erro no parser: {}", e);
            return;
        }
    };

    println!("Fórmula: {}", pretty_print_formula(&phi));
    println!();

    // 1) TABLEAU para T(φ) — satisfatibilidade
    println!("--- TABLEAU para T(φ) — testa satisfatibilidade de φ ---");
    let mut ctx = TableauContext::new();
    let root_branch = TableauBranch::new(vec![Signed::new(Sign::T, phi.clone())]);
    let root_node = expand_branch(root_branch, &mut ctx);
    print_proof_node(&root_node, 0, "R");
    if root_node.closed {
        println!("Resultado: Todos os ramos fecham ⇒ T(φ) é INSATISFATÍVEL (φ não é satisfatível).");
    } else {
        println!("Resultado: Existe ramo aberto ⇒ T(φ) é SATISFATÍVEL. Modelo parcial exibido no ramo aberto.");
    }

    // 2) TABLEAU para F(φ) — validade
    println!();
    println!("--- TABLEAU para F(φ) — testa validade de φ (se todos ramos fecham, φ é válida) ---");
    let mut ctx2 = TableauContext::new();
    let root_branch2 = TableauBranch::new(vec![Signed::new(Sign::F, phi.clone())]);
    let root_node2 = expand_branch(root_branch2, &mut ctx2);
    print_proof_node(&root_node2, 0, "R");
    if root_node2.closed {
        println!("Resultado: Todos os ramos fecham ⇒ F(φ) é INSATISFATÍVEL ⇒ φ É VÁLIDA.");
    } else {
        println!("Resultado: Existe ramo aberto ⇒ F(φ) é SATISFATÍVEL ⇒ φ NÃO é válida (contraexemplo parcial exibido).");
    }
}
