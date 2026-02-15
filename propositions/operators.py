# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5

    #ДНФ
    variables = sorted(formula.variables())
    models = all_models(variables)
    
    if not variables:
        if evaluate(formula, {}):
            p = Formula('p') # делает всегда верную функцию (константа), так как нельзя константы
            return Formula('|', p, Formula('~', p))
        else:
            p = Formula('p') # делает всегда неверную функцию (константа), так как нельзя константы
            return Formula('&', p, Formula('~', p))

    disjuncts = []
    for model in models:
        if evaluate(formula, model):
            conjuncts = []
            for var in variables:
                if model[var]:
                    conjuncts.append(Formula(var))
                else:
                    conjuncts.append(Formula('~', Formula(var)))
            if conjuncts:
                conj = conjuncts[0]
                for c in conjuncts[1:]:
                    conj = Formula('&', conj, c)
                disjuncts.append(conj)
    
    if not disjuncts: # делает всегда неверную функцию (противоречивость), так как нельзя константы
        return Formula('&', Formula('p'), Formula('~', Formula('p')))
    
    result = disjuncts[0]
    for d in disjuncts[1:]:
        result = Formula('|', result, d)
    
    return result

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a

    # Делаем днф как в прошлой задаче и меняем p|q = ~(~p & ~q)
    f = to_not_and_or(formula)
    
    if is_variable(f.root) or is_constant(f.root):
        return f
    if is_unary(f.root):
        return Formula('~', to_not_and(f.first))
    if f.root == '&':
        return Formula('&', to_not_and(f.first), to_not_and(f.second))
    if f.root == '|':
        left = to_not_and(f.first)
        right = to_not_and(f.second)
        not_left = Formula('~', left)
        not_right = Formula('~', right)
        return Formula('~', Formula('&', not_left, not_right))
    return f

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b

    # Делаем днф и меняем формулы на штрих Шеффера
    f = to_not_and_or(formula)
    
    if is_variable(f.root):
        return f
        
    if is_unary(f.root):  # ~p = (p -& p)
        inner = to_nand(f.first)
        return Formula('-&', inner, inner)
        
    if f.root == '&':  # p & q = ((p -& q) -& (p -& q))
        left = to_nand(f.first)
        right = to_nand(f.second)
        nand = Formula('-&', left, right)
        return Formula('-&', nand, nand)
        
    if f.root == '|':  # p | q = ((p -& p) -& (q -& q))
        left = to_nand(f.first)
        right = to_nand(f.second)
        left_nand = Formula('-&', left, left)
        right_nand = Formula('-&', right, right)
        return Formula('-&', left_nand, right_nand)
        
    return f

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c

    #Аналогично с предыдущими заданиями
    f = to_not_and_or(formula)

    if is_variable(f.root):
        return f
        
    if is_unary(f.root):
        return Formula('~', to_implies_not(f.first))
        
    if f.root == '&':  # p & q = ~(p -> ~q)
        left = to_implies_not(f.first)
        right = to_implies_not(f.second)
        not_right = Formula('~', right)
        imp = Formula('->', left, not_right)
        return Formula('~', imp)
        
    if f.root == '|':  # p | q = ~p -> q
        left = to_implies_not(f.first)
        right = to_implies_not(f.second)
        not_left = Formula('~', left)
        return Formula('->', not_left, right)
        
    return f

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d

    # аналогично предыдущим заданиям
    f = to_not_and_or(formula)
    
    if is_variable(f.root):
        return f
        
    if f.root == '~': # ~p = (p -> F)
        inner = to_implies_false(f.first)
        return Formula('->', inner, Formula('F'))
        
    if f.root == '&': # p & q = ((p -> (q -> F)) -> F)
        left = to_implies_false(f.first)
        right = to_implies_false(f.second)
        q_imp_F = Formula('->', right, Formula('F'))
        p_imp_q_imp_F = Formula('->', left, q_imp_F)
        return Formula('->', p_imp_q_imp_F, Formula('F'))
        
    if f.root == '|': # p | q = ((p -> F) -> q)
        left = to_implies_false(f.first)
        right = to_implies_false(f.second)
        p_imp_F = Formula('->', left, Formula('F'))
        return Formula('->', p_imp_F, right)
        
    return f