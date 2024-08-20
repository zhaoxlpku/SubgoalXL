import json
import re

import requests
import sympy as sp
import timeout_decorator
from sympy import symbols, simplify, Eq
from sympy.logic.boolalg import And
from sympy.parsing.sympy_parser import parse_expr

from utils.prompt_utils import last_boxed_only_string, remove_boxed


@timeout_decorator.timeout(5)
def extract_objective(sample_string):
    # Define the regular expression pattern for (1)
    pattern1 = r'shows\s*"([^"]*)"'

    # Use re.search() to find the first match of pattern1
    match1 = re.search(pattern1, sample_string)

    # If pattern (1) is found, extract and return it
    if match1:
        # print("match1")
        # print(match1.group(1))
        return match1.group(1)
    else:
        # If pattern (1) is not found, look for pattern (2)
        pattern2 = r'"([^"]*)"'
        match2 = re.search(pattern2, sample_string)
        # If pattern (2) is found, extract and return it
        if match2:
            # print("match2")
            # print(match2.group(1))
            return match2.group(1)
        else:
            return None  # Neither pattern (1) nor pattern (2) found


def is_valid_case(formal_statement, formal_proof=None):
    try:
        if len(formal_statement.strip().split("\n")) == 1: # bad case
            return False
        obj = extract_objective(formal_statement)
        if obj is None:
            return False
        if "shows" in formal_statement:
            last_line = formal_statement.split("\n")[-1].strip()
            if "shows" in formal_statement.split("\n")[-1]:
                if not last_line.endswith('"'):
                    return False
            else:
                if not last_line[:-1].strip() in obj:
                    if not (last_line.startswith('and ') and last_line.endswith('"')):
                        return False
        else:
            line1 = formal_statement.strip().split("\n")[0].strip()
            line2 = formal_statement.strip().split("\n")[1].strip()
            if not line1.startswith("theorem") or line2[1:-1] != obj.strip():
                return False
        return True
    except KeyboardInterrupt:
        raise
    except timeout_decorator.timeout_decorator.TimeoutError:
        return True
    except Exception:
        return True

@timeout_decorator.timeout(5)
def contains_variables(expression):
    expression = re.sub(r"::\w+", "", expression)
    pattern = r'[a-zA-Z]\w*'
    match = re.search(pattern, expression)
    return match is not None

@timeout_decorator.timeout(60)
def contains_removable_variable(expression):
    try:
        operators = ["=", "<", ">", "<=", ">=", "!="]
        operator = None
        for op in operators:
            if op in expression:
                operator = op
                break

        if not operator:
            return False
        
        left_side, right_side = expression.split(operator)
        left_expr = sp.sympify(left_side.strip())
        right_expr = sp.sympify(right_side.strip())
        variables = left_expr.free_symbols.union(right_expr.free_symbols)
        left_coeffs = {var: left_expr.coeff(var) for var in variables}
        right_coeffs = {var: right_expr.coeff(var) for var in variables}
        if len(left_coeffs) == 0 or len(right_coeffs) == 0:
            return False
        for var in variables:
            if left_coeffs[var] != right_coeffs[var] or left_coeffs[var] == 0:
                return False
        return True
    except KeyboardInterrupt:
        raise
    except Exception:
        return False
    # except (sp.SympifyError, TypeError, ValueError, ZeroDivisionError, AttributeError, CoercionFailed, ComputationFailed, PolynomialError, NotImplementedError) as e:
    #     return False

def is_nontrivial_case(formal_statement, formal_proof=None):
    try:
        if len(formal_statement.strip().split("\n")) == 1: # bad case
            return False
        obj = extract_objective(formal_statement)
        if obj is None:
            return False
        if not contains_variables(obj):
            return False
        if contains_removable_variable(obj):
            return False
        return True
    # except timeout_decorator.timeout_decorator.TimeoutError:
    #     return True
    except KeyboardInterrupt:
        raise
    except timeout_decorator.timeout_decorator.TimeoutError:
        return True
    except Exception:
        return True

@timeout_decorator.timeout(5)
def extract_isabelle_expressions(statement):
    pattern = r'"(.*?)"'
    expressions = re.findall(pattern, statement)
    return expressions


def preprocess_expression(expression):
    expression = expression.replace("div", "//")
    expression = expression.replace("mod", "%")
    # expression = re.sub(r"\\<Sum>\s*k\s*<\s*n\s*\.\s*([^)]*)", r"Sum(\1, (k, 0, n-1))", expression)
    expression = expression.replace("\\<ge>", ">=")
    expression = expression.replace("\\<le>", "<=")
    expression = re.sub(r"::\w+", "", expression)
    expression = re.sub(r":: \w+", "", expression)
    expression = expression.replace("'", "prime")
    return expression


def identify_contradictions(parsed_expressions):
    combined_expression = And(*parsed_expressions)
    contradiction = simplify(combined_expression)
    if contradiction == False:
        return True, "Logical inconsistencies within expressions make cases contradictory."
    else:
        return False, None
    
@timeout_decorator.timeout(60)
def check_contradictions(expressions):
    try:
        expressions = [preprocess_expression(expr) for expr in expressions]
        all_symbols = set()
        for expr in expressions:
            all_symbols.update(re.findall(r'\b\w+\b', expr))
        
        symbol_dict = {s: symbols(s) for s in all_symbols}
        # parsed_expressions = [sympify(expr, locals=symbol_dict) for expr in expressions]
        parsed_expressions = []
        for expr in expressions:
            # expr = eval(expr, symbol_dict) # new feature
            if "=" in expr:
                left, right = expr.split("=")
                parsed_expressions.append(Eq(parse_expr(left, local_dict=symbol_dict), parse_expr(right, local_dict=symbol_dict)))
            else:
                parsed_expressions.append(parse_expr(expr, local_dict=symbol_dict))
        return identify_contradictions(parsed_expressions)
    # except (ValueError, SyntaxError, TypeError, tokenize.TokenError, ZeroDivisionError, AttributeError, CoercionFailed, ComputationFailed, PrecisionExhausted, PolynomialError):
    #     return False, None
    except KeyboardInterrupt:
        raise
    except Exception:
        return False, None

def num_tokens_from_string(tokenizer, string: str) -> int:
    return len(tokenizer.encode(string))

def isabelle_statement_checker(formal_statement, endpoint, tokenizer, demonstration, use_chat=False):
    if not use_chat:
        prompt = f"{demonstration}\n\n---\n\n### Input\n{formal_statement}\n\n### Output"
        stop_sequences = ["---", "### Input", '<｜end▁of▁sentence｜>']
    else:
        system = "Verify if the objective is a trivial consequence of the assumptions, unrelated, or leads to a contradiction, and classify the statement as either $\\boxed{good}$ or $\\boxed{bad}$."
        chat_history = [{"role": "system", "content": system}]
        demos = demonstration.split("---")
        for demo in demos:
            user = demo.split("### Output")[0].split("### Input")[1].strip()
            assistant = demo.split("### Output")[1].strip()
            chat_history.append(
                {"role": "user", "content": user},
            )
            chat_history.append(
                {"role": "assistant", "content": assistant},
            )
        chat_history.append(
            {"role": "user", "content": formal_statement}
        )
        prompt = tokenizer.apply_chat_template(chat_history, tokenize=False)
        stop_sequences = ['<｜end▁of▁sentence｜>']
    
    max_tokens = 4086 - num_tokens_from_string(tokenizer, prompt)
    if max_tokens <= 10: 
        return False, "Excessive statement length indicates flaws or ambiguities in cases."
    response = requests.post(f'http://{endpoint}/completions', json={
        "prompt": prompt,
        "n": 1,
        "do_sample": False,
        "max_tokens": max_tokens,
        "stop_sequences": stop_sequences,
    })
    response = json.loads(response.text)
    response_text = response['choices'][0]['text']
    if response_text.startswith("assistant"):
        response_text = response_text.split("assistant")[1].strip()
    result = remove_boxed(last_boxed_only_string(response_text))
    # print(response_text)
    # print("------")
    # print(result)
    if isinstance(result, str) and result.strip() == "good":
        return True, response_text
    else:
        return False, response_text

def is_good_case(formal_statement, endpoint, tokenizer, demonstration, use_chat=False):
    try:
        expressions = extract_isabelle_expressions(formal_statement)
        is_contradicted, message = check_contradictions(expressions)
    except timeout_decorator.timeout_decorator.TimeoutError:
        is_contradicted = True
        message = "Overly complex expressions likely contain structural issues."
    if is_contradicted: return False, message

    return isabelle_statement_checker(
        formal_statement=formal_statement, 
        endpoint=endpoint, 
        tokenizer=tokenizer, 
        demonstration=demonstration,
        use_chat=use_chat,
    )
