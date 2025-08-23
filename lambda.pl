use_module(library(ordsets)).
:- dynamic macro/2.

% Grammar (right-associative abstraction, left-associative application)
program(E) --> macro_def, program(E).
program(E) --> expression(E).
expression(E) -->
	atomic_expr(A),
	expression_rest(A, E).
expression_rest(Acc, E) -->
	atomic_expr(A),
	expression_rest(app(Acc, A), E). 
expression_rest(E, E) --> [].

atomic_expr(E) --> macro_name(M, N), { macro(M, E0), macro_expand(E0, N, E) }.
atomic_expr(E) --> macro_name(M), { macro(M, E) }.
atomic_expr(E) --> abstraction(E).
atomic_expr(E) --> variable(E).
atomic_expr(E) --> repeat(E).
atomic_expr(E) --> ['('], expression(E), [')'].

repeat(rep(E)) --> ['['], expression(E), [']'].
abstraction(abs(V, E)) -->
	['λ'], binder(V),
	['.'], expression(E).
variable(vari(V)) -->
	[V],
	{ atom(V), atom_chars(V, [C|_]), char_type(C, alpha) }.
binder(bind(V)) -->
	[V],
	{ atom(V), atom_chars(V, [C|_]), char_type(C, alpha) }.

% Macros
macro_def --> ['#'], macro_name(M), ['{'], expression(AST), ['}'], { retractall(macro(M, _)), assertz(macro(M, AST)) }.

macro_name(M, N) -->
	[M], ['['], [N0], [']'],
	{ atom(M), atom_number(N0, N) }.

macro_name(M) -->
	[M],
	{ atom(M) }.

% Right-associative application macro expansion
macro_expand(app(rep(_), E), 0, E).
macro_expand(rep(E), 1, E).
macro_expand(vari(V), _, vari(V)).
macro_expand(abs(V, E0), N, abs(V, E)) :- macro_expand(E0, N, E). 
macro_expand(app(rep(E1), E2), N0, E) :- N is N0 - 1, macro_expand(app(E1, E2), rep(E1), N, E). 
macro_expand(app(E1, E2), N, app(E3, E4)) :- macro_expand(E1, N, E3), macro_expand(E2, N, E4). 
macro_expand(rep(E0), N0, E) :- N is N0 - 1, macro_expand(E0, rep(E0), N, E).

macro_expand(Acc, _, 0, Acc). 
macro_expand(Acc, rep(E0), N0, E) :- N is N0 - 1, macro_expand(app(E0, Acc), rep(E0), N, E). 

% Beta-Reduction (normal-order)
beta_reduce(app(abs(Binder, Expr), Arg), R) :- substitute(Binder, Expr, Arg, R). 
beta_reduce(app(E1, E2), app(R, E2)) :- beta_reduce(E1, R).
beta_reduce(app(E1, E2), app(E1, R)) :- beta_reduce(E2, R).
beta_reduce(abs(V, E), abs(V, R)) :- beta_reduce(E, R).
normal_form(E, R) :- beta_reduce(E, E1), normal_form(E1, R). 
normal_form(E, E). 

% Abstraction
substitute(bind(V), abs(bind(V), E), _,   abs(bind(V), E)).
substitute(bind(V), abs(bind(W), E), Arg, abs(bind(W), E2)) :-
	V \= W,
	free_variables(Arg, FVArg),
	\+ ord_memberchk(W, FVArg),
	substitute(bind(V), E, Arg, E2).
substitute(bind(V), abs(bind(W), E), Arg, abs(bind(Fresh), E2)) :-
	V \= W,
	free_variables(Arg, FVArg),
	ord_memberchk(W, FVArg),
	free_variables(E, FVE),
	ord_union(FVE, FVArg, Used0),
	ord_add_element(Used0, V, Used),
	fresh_variable(Used, Fresh),
	rename_var(W, Fresh, E, E0),
	substitute(bind(V), E0, Arg, E2).
 
% Alpha-Reductionless version of the above 2 abstraction substitution rules. 
% Note: This is susceptible to erroneous variable capture!
% substitute(bind(V), abs(bind(W), E), Arg, abs(bind(W), E2)) :-
% 	V \= W,
% 	substitute(bind(V), E, Arg, E2).

% Application
substitute(bind(V), app(E1, E2), Arg, app(E3, E4)) :- substitute(bind(V), E1, Arg, E3), substitute(bind(V), E2, Arg, E4).

% Variable
substitute(bind(V), vari(V), Arg, Arg).
substitute(bind(V), vari(W), _,   vari(W)) :- V \= W.

% Free Variables and Alpha-Conversion
free_variables(abs(bind(V), E), D) :- free_variables(E, S1), list_to_ord_set([V], S2), ord_subtract(S1, S2, D).
free_variables(app(E1, E2), U) :- free_variables(E1, S1), free_variables(E2, S2), ord_union(S1, S2, U).
free_variables(vari(V), S) :- list_to_ord_set([V], S).

variable_set(S) :- list_to_ord_set([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z], S).

fresh_variable(Used, Fresh) :- variable_set(All), ord_subtract(All, Used, [Fresh|_]).

rename_var(Old, New, abs(bind(Old), E), abs(bind(New), E2)) :- rename_var(Old, New, E, E2).
rename_var(Old, New, abs(V, E), abs(V, E2)) :- rename_var(Old, New, E, E2).

rename_var(Old, New, app(E1, E2), app(E3, E4)) :- rename_var(Old, New, E1, E3), rename_var(Old, New, E2, E4).

rename_var(Old, New, vari(Old), vari(New)).
rename_var(Old, _, vari(V), vari(V)) :- Old \= V.

alpha_equivalent(E1, E2) :- alpha_equivalent(E1, E2, []).
alpha_equivalent(vari(V1), vari(V2), Env) :- member(V1-V2, Env). 
alpha_equivalent(vari(V), vari(V), Env) :- \+ member(V-_, Env), \+ member(_-V, Env). 
alpha_equivalent(abs(bind(V1), E1), abs(bind(V2), E2), Env) :- alpha_equivalent(E1, E2, [V1-V2|Env]).
alpha_equivalent(app(E1, E2), app(E3, E4), Env) :- alpha_equivalent(E1, E3, Env), alpha_equivalent(E2, E4, Env).

% Tokenization
% tokenize(S, R) :- string_chars(S, C), exclude(whitespace, C, R).
tokenize(S, T) :- string_chars(S, C), phrase(tokens(T), C).

tokens([]) --> [].
tokens([T|Ts]) --> whitespace_chars, token(T), whitespace_chars, tokens(Ts).

token(T) --> [T], { atomic_char(T) }.
token(T) --> word_chars(C), { atom_chars(T, C) }.

whitespace_chars --> [C], { whitespace(C) }, whitespace_chars.
whitespace_chars --> [].

word_chars([C|Cs]) --> [C], { \+ whitespace(C), \+ atomic_char(C) }, word_chars(Cs). 
word_chars([]) --> [].

atomic_char('λ').
atomic_char('.').
atomic_char('(').
atomic_char(')').
atomic_char('{').
atomic_char('}').
atomic_char('[').
atomic_char(']').
atomic_char('#').

whitespace(' ').
whitespace('\n').
whitespace('\t').

% Top Level
% Generate AST
file_to_AST(F, AST) :- read_file_to_string(F, S, []), string_to_AST(S, AST). 
string_to_AST(S, AST) :- tokenize(S, T), phrase(program(AST), T).
% Evaluate to normal form
evaluate_string(S, NAST) :- string_to_AST(S, AST), normal_form(AST, NAST).
evaluate_file(S, NAST) :- file_to_AST(S, AST), normal_form(AST, NAST). 
% Debug
debug_file(F, NAST) :- debug_file(F, NAST, false).
debug_file(F, NAST, Expand) :- file_to_AST(F, AST), debug_AST(AST, NAST, Expand).

debug_string(S, NAST) :- debug_string(S, NAST, false).
debug_string(S, NAST, Expand) :- string_to_AST(S, AST), debug_AST(AST, NAST, Expand).

debug_AST(AST, NAST) :- debug_AST(AST, NAST, false).
debug_AST(AST, NAST, Expand) :- print_AST(AST, Expand), write('\n\n'), normal_form_print(AST, NAST, Expand).
normal_form_print(E, R, Expand) :- beta_reduce(E, E1), print_AST(E1, Expand), write('\n\n'), normal_form_print(E1, R, Expand). 
normal_form_print(E, E, _).

debug_file_step(F, NAST) :- debug_file_step(F, NAST, false).
debug_file_step(F, NAST, Expand) :- file_to_AST(F, AST), debug_AST_step(AST, NAST, Expand).

debug_string_step(S, NAST) :- debug_string_step(S, NAST, false).
debug_string_step(S, NAST, Expand) :- string_to_AST(S, AST), debug_AST_step(AST, NAST, Expand).

debug_AST_step(AST, NAST) :- debug_AST_step(AST, NAST, false).
debug_AST_step(AST, NAST, Expand) :- print_AST(AST, Expand), get_single_char(_), write('\n\n'), normal_form_print_step(AST, NAST, Expand).
normal_form_print_step(E, R, Expand) :- beta_reduce(E, E1), print_AST(E1, Expand), get_single_char(_), write('\n\n'), normal_form_print_step(E1, R, Expand). 
normal_form_print_step(E, E, _).

% Pretty Printer (Unparser)
print_AST(E) :- print_AST(E, false).
print_AST(E, false) :- macro(M, AST), alpha_equivalent(E, AST), write(M).

% Finds and prints parameterized macros
% TODO: If alpha-conversion occured during execution, some macros will not be identified correctly. See: Multiplication as the B combinator, applied to Nums.
% GOAL: Implement alpha-normalization, so that the Macro AST and the given AST will be easier to identify as equal.
print_AST(E0, false) :-
	macro(M, MAST0),
	remove_reps(MAST0, MAST, L),
	flatten_app_chain(E0, E, L, C),
	alpha_equivalent(E, MAST),
	write(M), write('['), write(C), write(']').

print_AST(abs(V, E), Expand) :- write('('), print_AST(V, Expand), write('.'), print_AST(E, Expand), write(')').
print_AST(app(E1, E2), Expand) :- write('('), print_AST(E1, Expand), write(' '), print_AST(E2, Expand), write(')').
print_AST(vari(V), _) :- write(V).
print_AST(bind(V), _) :- write('λ'), write(V).


% The following rules are used to compare parameterized macro ASTs to a flattened AST (unused due to commented out print_AST call)

% This is probably flawed with sub-lambdas. EX: λn.(λy.y)((λz.z)n). n, y, and z all have the same index: 1.
% bruijin_indices(AST, L) :- bruijin_indices(AST, L, 0).
% bruijin_indices(rep(E), L, C) :- bruijin_indices(E, L, C).
% bruijin_indices(app(E1, E2), L, C) :- bruijin_indices(E1, L1, 0), bruijin_indices(E2, L2, 0), append(L1, L2, L).
% bruijin_indices(abs(bind(V), E), [V-C|L], C0) :- C is C0 + 1, bruijin_indices(E, L, C).
% bruijin_indices(vari(_), [], _).

% bruijin_form(AST0, AST).

remove_reps(rep(E0), E, [E0|Rs]) :- remove_reps(E0, E, Rs).
remove_reps(abs(V, E0), abs(V, E), L) :- remove_reps(E0, E, L).
remove_reps(app(E1, E2), app(E3, E4), L) :- remove_reps(E1, E3, L1), remove_reps(E2, E4, L2), append(L1, L2, L).
remove_reps(vari(V), vari(V), []).

% Right-associative application chains are flattened
flatten_app_chain(vari(V), vari(V), L, 1) :- member(vari(V), L).
flatten_app_chain(vari(V), vari(V), _, 0).
flatten_app_chain(abs(V, E0), abs(V, E), L, C) :- flatten_app_chain(E0, E, L, C).
flatten_app_chain(app(F, E0), app(F, E), L, C) :-
    member(F, L),
    flatten_app_chain_rest(E0, E, L, C0),
    C is C0 + 1.
flatten_app_chain_rest(app(F, E0), E, L, C) :-
    member(F, L),
    flatten_app_chain_rest(E0, E, L, C0),
    C is C0 + 1.
flatten_app_chain_rest(vari(V), vari(V), L, 1) :- member(vari(V), L).
flatten_app_chain_rest(vari(V), vari(V), _, 0).
klatten_app_chain_rest(app(F, E), app(F, E), _, 0). 
