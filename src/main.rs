use std::collections::{HashMap, HashSet};
use std::env;
use std::io::{self, Read};

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
    End,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Prop {
    Var(String),
    Not(Box<Prop>),
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
    Imp(Box<Prop>, Box<Prop>),
    Iff(Box<Prop>, Box<Prop>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Sign {
    T,
    F,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Signed {
    sign: Sign,
    formula: Prop,
}

impl Signed {
    fn new(sign: Sign, formula: Prop) -> Self {
        Signed { sign, formula }
    }
}

// ------------------ LEXER ------------------
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
        if i + 2 < n {
            if chs[i] == '<' && chs[i+1] == '-' && chs[i+2] == '>' {
                tokens.push(Token::Iff);
                i += 3;
                continue;
            }
        }
        if i + 1 < n {
            if chs[i] == '-' && chs[i+1] == '>' {
                tokens.push(Token::Imp);
                i += 2;
                continue;
            }
        }

        match c {
            '(' => { tokens.push(Token::LPar); i += 1; }
            ')' => { tokens.push(Token::RPar); i += 1; }
            '~' | '!' => { tokens.push(Token::Not); i += 1; }
            '&' | '∧' => { tokens.push(Token::And); i += 1; }
            '|' | 'v' | 'V' | '∨' => { tokens.push(Token::Or); i += 1; }
            '/' => {
                if i + 1 < n && chs[i+1] == '\\' { tokens.push(Token::And); i += 2; }
                else { i += 1; }
            }
            '\\' => {
                if i + 1 < n && chs[i+1] == '/' { tokens.push(Token::Or); i += 2; }
                else { i += 1; }
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
                    i += 1;
                }
            }
        }
    }

    tokens.push(Token::End);
    tokens
}

// ------------------ PARSER ------------------
struct Parser {
    toks: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn new(toks: Vec<Token>) -> Self { Parser { toks, pos: 0 } }

    fn peek(&self) -> &Token { &self.toks[self.pos] }

    fn bump(&mut self) {
        if self.pos < self.toks.len() { self.pos += 1; }
    }

    fn eat(&mut self, expected: &Token) -> bool {
        if self.peek() == expected {
            self.bump();
            true
        } else { false }
    }

    fn parse(&mut self) -> Result<Prop, String> { self.parse_iff() }

    fn parse_iff(&mut self) -> Result<Prop, String> {
        let mut left = self.parse_imp()?;
        while let Token::Iff = self.peek() {
            self.bump();
            let right = self.parse_imp()?;
            left = Prop::Iff(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn parse_imp(&mut self) -> Result<Prop, String> {
        let left = self.parse_or()?;
        if let Token::Imp = self.peek() {
            self.bump();
            let right = self.parse_imp()?;
            Ok(Prop::Imp(Box::new(left), Box::new(right)))
        } else { Ok(left) }
    }

    fn parse_or(&mut self) -> Result<Prop, String> {
        let mut left = self.parse_and()?;
        loop {
            match self.peek() {
                Token::Or => { self.bump(); let r = self.parse_and()?; left = Prop::Or(Box::new(left), Box::new(r)); }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_and(&mut self) -> Result<Prop, String> {
        let mut left = self.parse_unary()?;
        loop {
            match self.peek() {
                Token::And => { self.bump(); let r = self.parse_unary()?; left = Prop::And(Box::new(left), Box::new(r)); }
                _ => break,
            }
        }
        Ok(left)
    }

    fn parse_unary(&mut self) -> Result<Prop, String> {
        match self.peek() {
            Token::Not => { self.bump(); let inner = self.parse_unary()?; Ok(Prop::Not(Box::new(inner))) }
            Token::LPar => {
                self.bump();
                let expr = self.parse()?;
                if !self.eat(&Token::RPar) { return Err("Parênteses não fechados".to_string()); }
                Ok(expr)
            }
            Token::Ident(name) => {
                let n = name.clone();
                self.bump();
                Ok(Prop::Var(n))
            }
            _ => Err(format!("Token inesperado: {:?}", self.peek())),
        }
    }
}

fn pretty_print_prop(p: &Prop) -> String {
    match p {
        Prop::Var(s) => s.clone(),
        Prop::Not(a) => format!("¬{}", pretty_print_prop(a)),
        Prop::And(a,b) => format!("({} ∧ {})", pretty_print_prop(a), pretty_print_prop(b)),
        Prop::Or(a,b) => format!("({} ∨ {})", pretty_print_prop(a), pretty_print_prop(b)),
        Prop::Imp(a,b) => format!("({} → {})", pretty_print_prop(a), pretty_print_prop(b)),
        Prop::Iff(a,b) => format!("({} ↔ {})", pretty_print_prop(a), pretty_print_prop(b)),
    }
}

fn pretty_print_signed(s: &Signed) -> String {
    let sign = match s.sign {
        Sign::T => "T",
        Sign::F => "F",
    };
    format!("{} {}", sign, pretty_print_prop(&s.formula))
}

fn is_literal(s: &Signed) -> bool {
    match &s.formula {
        Prop::Var(_) => true,
        Prop::Not(inner) => match &**inner {
            Prop::Var(_) => true,
            _ => false,
        },
        _ => false,
    }
}

#[derive(Debug, Clone)]
struct TableauBranch {
    formulas: Vec<Signed>,
    applied: HashSet<Signed>,
}

impl TableauBranch {
    fn new(initial: Vec<Signed>) -> Self {
        TableauBranch { formulas: initial, applied: HashSet::new() }
    }

    fn contains_contradiction(&self) -> bool {
        let mut tvars = HashSet::new();
        let mut fvars = HashSet::new();
        for s in &self.formulas {
            match &s.formula {
                Prop::Var(name) => {
                    match s.sign {
                        Sign::T => { tvars.insert(name.clone()); }
                        Sign::F => { fvars.insert(name.clone()); }
                    }
                }
                Prop::Not(inner) => {
                    if let Prop::Var(name) = &**inner {
                        match s.sign {
                            Sign::T => { fvars.insert(name.clone()); }
                            Sign::F => { tvars.insert(name.clone()); }
                        }
                    }
                }
                _ => {}
            }
        }
        !tvars.is_disjoint(&fvars)
    }

    fn find_contradiction_var(&self) -> Option<String> {
        let mut tvars = HashSet::new();
        let mut fvars = HashSet::new();
        for s in &self.formulas {
            match &s.formula {
                Prop::Var(name) => {
                    match s.sign {
                        Sign::T => { tvars.insert(name.clone()); }
                        Sign::F => { fvars.insert(name.clone()); }
                    }
                }
                Prop::Not(inner) => {
                    if let Prop::Var(name) = &**inner {
                        match s.sign {
                            Sign::T => { fvars.insert(name.clone()); }
                            Sign::F => { tvars.insert(name.clone()); }
                        }
                    }
                }
                _ => {}
            }
        }
        for v in tvars {
            if fvars.contains(&v) {
                return Some(v);
            }
        }
        None
    }

    fn is_closed(&self) -> bool {
        self.contains_contradiction()
    }

    fn all_literals(&self) -> bool {
        self.formulas.iter().all(|s| is_literal(s))
    }
}

enum Expansion {
    Add(Vec<Signed>),
    Branch(Vec<Signed>, Vec<Signed>),
    None,
}

fn expand_signed(signed: &Signed) -> (Expansion, &'static str) {
    use Prop::*;
    use Sign::*;
    match (&signed.sign, &signed.formula) {
        (T, And(a,b)) => (Expansion::Add(vec![Signed::new(T, (*a.clone()).clone()), Signed::new(T, (*b.clone()).clone())]), "Regra T-∧ (α): T(A∧B) => T A, T B"),
        (F, Or(a,b)) => (Expansion::Add(vec![Signed::new(F, (*a.clone()).clone()), Signed::new(F, (*b.clone()).clone())]), "Regra F-∨ (α): F(A∨B) => F A, F B"),
        (T, Or(a,b)) => (Expansion::Branch(vec![Signed::new(T, (*a.clone()).clone())], vec![Signed::new(T, (*b.clone()).clone())]), "Regra T-∨ (β): T(A∨B) => ramo: T A  |  T B"),
        (F, And(a,b)) => (Expansion::Branch(vec![Signed::new(F, (*a.clone()).clone())], vec![Signed::new(F, (*b.clone()).clone())]), "Regra F-∧ (β): F(A∧B) => ramo: F A  |  F B"),
        (T, Imp(a,b)) => (Expansion::Branch(vec![Signed::new(F, (*a.clone()).clone())], vec![Signed::new(T, (*b.clone()).clone())]), "Regra T-→ (β): T(A→B) => ramo: F A  |  T B"),
        (F, Imp(a,b)) => (Expansion::Add(vec![Signed::new(T, (*a.clone()).clone()), Signed::new(F, (*b.clone()).clone())]), "Regra F-→ (α): F(A→B) => T A, F B"),
        (T, Not(a)) => (Expansion::Add(vec![Signed::new(F, (*a.clone()).clone())]), "Regra T-¬: T¬A => F A"),
        (F, Not(a)) => (Expansion::Add(vec![Signed::new(T, (*a.clone()).clone())]), "Regra F-¬: F¬A => T A"),
        (T, Iff(a,b)) => (Expansion::Branch(
            vec![Signed::new(T, (*a.clone()).clone()), Signed::new(T, (*b.clone()).clone())],
            vec![Signed::new(F, (*a.clone()).clone()), Signed::new(F, (*b.clone()).clone())],
        ), "Regra T-↔ (β): T(A↔B) => ramo: (T A, T B)  |  (F A, F B)"),
        (F, Iff(a,b)) => (Expansion::Branch(
            vec![Signed::new(T, (*a.clone()).clone()), Signed::new(F, (*b.clone()).clone())],
            vec![Signed::new(F, (*a.clone()).clone()), Signed::new(T, (*b.clone()).clone())],
        ), "Regra F-↔ (β): F(A↔B) => ramo: (T A, F B)  |  (F A, T B)"),
        _ => (Expansion::None, "Sem regra (literal ou não expansível)"),
    }
}

fn choose_unexpanded(branch: &TableauBranch) -> Option<Signed> {
    for s in &branch.formulas {
        if is_literal(s) { continue; }
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

#[derive(Clone, Debug)]
struct ProofNode {
    formulas: Vec<Signed>,
    expanded: Option<Signed>,
    rule: Option<String>,
    additions: Vec<Vec<Signed>>, // for add: one vec; for branch: two vecs
    children: Vec<ProofNode>,
    closed: bool,
    model: Option<HashMap<String,bool>>,
}

fn expand_branch(mut br: TableauBranch) -> ProofNode {
    // If branch closed immediately
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

    match choose_unexpanded(&br) {
        None => {
            // fully expanded => open branch (model found)
            let model = build_model_from_formulas(&br.formulas);
            ProofNode {
                formulas: br.formulas.clone(),
                expanded: None,
                rule: None,
                additions: vec![],
                children: vec![],
                closed: false,
                model,
            }
        }
        Some(s) => {
            // mark applied
            br.applied.insert(s.clone());
            let (expansion, rule_name) = expand_signed(&s);
            match expansion {
                Expansion::None => {
                    // nothing to expand (shouldn't occur frequently); try continue
                    expand_branch(br)
                }
                Expansion::Add(to_add) => {
                    let mut new_br = br.clone();
                    add_unique(&mut new_br.formulas, to_add.clone());
                    let child = expand_branch(new_br);
                    ProofNode {
                        formulas: br.formulas.clone(),
                        expanded: Some(s),
                        rule: Some(rule_name.to_string()),
                        additions: vec![to_add],
                        children: vec![child.clone()],
                        closed: child.closed,
                        model: if !child.closed { child.model.clone() } else { None },
                    }
                }

                Expansion::Branch(left_add, right_add) => {
                    let mut left_br = br.clone();
                    add_unique(&mut left_br.formulas, left_add.clone());
                    let left_node = expand_branch(left_br);

                    let mut right_br = br.clone();
                    add_unique(&mut right_br.formulas, right_add.clone());
                    let right_node = expand_branch(right_br);

                    let closed_all = left_node.closed && right_node.closed;
                    let chosen_model = if !left_node.closed { left_node.model.clone() } else if !right_node.closed { right_node.model.clone() } else { None };

                    ProofNode {
                        formulas: br.formulas.clone(),
                        expanded: Some(s),
                        rule: Some(rule_name.to_string()),
                        additions: vec![left_add, right_add],
                        children: vec![left_node, right_node],
                        closed: closed_all,
                        model: chosen_model,
                    }
                }
            }
        }
    }
}

fn build_model_from_formulas(formulas: &Vec<Signed>) -> Option<HashMap<String,bool>> {
    let mut model = HashMap::new();
    for s in formulas {
        match &s.formula {
            Prop::Var(name) => {
                match s.sign {
                    Sign::T => { model.insert(name.clone(), true); }
                    Sign::F => { model.insert(name.clone(), false); }
                }
            }
            Prop::Not(inner) => {
                if let Prop::Var(name) = &**inner {
                    match s.sign {
                        Sign::T => { model.insert(name.clone(), false); }
                        Sign::F => { model.insert(name.clone(), true); }
                    }
                }
            }
            _ => {}
        }
    }
    Some(model)
}

fn detect_contradiction_var_from_formulas(formulas: &Vec<Signed>) -> Option<String> {
    let mut tvars = HashSet::new();
    let mut fvars = HashSet::new();
    for s in formulas {
        match &s.formula {
            Prop::Var(name) => {
                match s.sign {
                    Sign::T => { tvars.insert(name.clone()); }
                    Sign::F => { fvars.insert(name.clone()); }
                }
            }
            Prop::Not(inner) => {
                if let Prop::Var(name) = &**inner {
                    match s.sign {
                        Sign::T => { fvars.insert(name.clone()); }
                        Sign::F => { tvars.insert(name.clone()); }
                    }
                }
            }
            _ => {}
        }
    }
    for v in tvars {
        if fvars.contains(&v) {
            return Some(v);
        }
    }
    None
}

fn print_proof_node(node: &ProofNode, indent: usize, label: &str) {
    let pad = " ".repeat(indent);
    // show label and formulas at this node (compact)
    if let Some(expanded) = &node.expanded {
        println!("{}{} - Expande: {}. Regra: {}", pad, label, pretty_print_signed(expanded), node.rule.as_ref().unwrap());
        // show additions
        if node.additions.len() == 1 {
            let added = &node.additions[0];
            let strs: Vec<String> = added.iter().map(|s| pretty_print_signed(s)).collect();
            println!("{}  => Adiciona: {}", pad, strs.join(", "));
            // print child
            if !node.children.is_empty() {
                print_proof_node(&node.children[0], indent + 4, &format!("{}·1", label));
            }
        } else if node.additions.len() == 2 {
            // branching: print children labeled 1 and 2
            let added_left: Vec<String> = node.additions[0].iter().map(|s| pretty_print_signed(s)).collect();
            let added_right: Vec<String> = node.additions[1].iter().map(|s| pretty_print_signed(s)).collect();
            println!("{}  => Cria dois ramos:", pad);
            println!("{}    Ramo 1 adiciona: {}", pad, added_left.join(", "));
            println!("{}    Ramo 2 adiciona: {}", pad, added_right.join(", "));
            // print both children
            if node.children.len() >= 1 {
                print_proof_node(&node.children[0], indent + 4, &format!("{}·1", label));
            }
            if node.children.len() >= 2 {
                print_proof_node(&node.children[1], indent + 4, &format!("{}·2", label));
            }
        }
    } else {
        // leaf
        if node.closed {
            // find contradiction var if possible
            if let Some(var) = detect_contradiction_var_from_formulas(&node.formulas) {
                println!("{}{} - Folha: Fechada (contradição em '{}').", pad, label, var);
            } else {
                println!("{}{} - Folha: Fechada (contradição).", pad, label);
            }
            // optionally list formulas that led à contradição (compact)
            let lits: Vec<String> = node.formulas.iter().map(|s| pretty_print_signed(s)).collect();
            println!("{}  Fórmulas no ramo: {}", pad, lits.join(", "));
        } else {
            println!("{}{} - Folha: Aberta (modelo parcial encontrado).", pad, label);
            if let Some(m) = &node.model {
                for (k,v) in m {
                    println!("{}  {} = {}", pad, k, v);
                }
            }
            let lits: Vec<String> = node.formulas.iter().map(|s| pretty_print_signed(s)).collect();
            println!("{}  Fórmulas no ramo: {}", pad, lits.join(", "));
        }
    }
}

fn main() {
    // Read input formula from args or stdin
    let args: Vec<String> = env::args().collect();
    let formula_str = if args.len() > 1 {
        args[1..].join(" ")
    } else {
        println!("Digite a fórmula (ex.: (p -> q) & p & !q):");
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

    println!("Fórmula: {}", pretty_print_prop(&phi));
    println!();
    // 1) Prova tableaux para T φ (satisfatibilidade)
    println!("--- TABLEAU para T(φ) — testa satisfatibilidade de φ ---");
    let root_branch = TableauBranch::new(vec![Signed::new(Sign::T, phi.clone())]);
    let root_node = expand_branch(root_branch);
    print_proof_node(&root_node, 0, "R");
    if root_node.closed {
        println!("Resultado: Todos os ramos fecham → T(φ) é INSATISFATÍVEL (φ NÃO tem modelo que a torne verdadeira).");
    } else {
        println!("Resultado: Existe ramo aberto → T(φ) é SATISFATÍVEL. Modelo parcial mostrado no ramo aberto.");
    }

    println!("\n--- TABLEAU para F(φ) — testa validade de φ (se todos ramos fecham, φ é válida) ---");
    let root_branch2 = TableauBranch::new(vec![Signed::new(Sign::F, phi.clone())]);
    let root_node2 = expand_branch(root_branch2);
    print_proof_node(&root_node2, 0, "R");
    if root_node2.closed {
        println!("Resultado: Todos os ramos fecham → F(φ) insatisfatível → φ É VÁLIDA.");
    } else {
        println!("Resultado: Existe ramo aberto → F(φ) satisfatível → φ NÃO é válida. Contraexemplo parcial mostrado no ramo aberto.");
    }
}