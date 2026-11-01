"""Experimental copy rank from the old value of the raw bit sequence.

This is a measurement adapter.  It loads a separate, flags-off instance of
token_value, so a copy-rank request cannot re-enter the flagged evaluator.
The old evaluator also assigns numbers to some non-standard raw sequences;
callers must not interpret those numbers as proven SSOS ordinals.
"""
import importlib.util
from pathlib import Path

from v_bits43 import bits

_spec = importlib.util.spec_from_file_location(
    '_p1_raw_old_token_value', Path(__file__).resolve().parent / 'token_value.py')
_old = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_old)


def rank(copies):
    raw = (0, 0) + bits(tuple(copies))
    try:
        return _old.value(raw)
    except _old.Unknown as error:
        raise ValueError(('raw bit value unknown', tuple(copies), raw, error.args)) from error
