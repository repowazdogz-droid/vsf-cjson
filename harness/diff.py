#!/usr/bin/env python3
"""Run both binaries on the same bytes and compare (exit code, stdout)."""
import subprocess, sys
ORACLE = "./oracle/cjson_oracle"
LEAN   = "./lean/.lake/build/bin/cjson"

def run(binary, data, timeout=10):
    try:
        p = subprocess.run([binary], input=data, capture_output=True, timeout=timeout)
        return p.returncode, p.stdout
    except subprocess.TimeoutExpired:
        return "TIMEOUT", b""

def compare(data):
    return run(ORACLE, data), run(LEAN, data)

if __name__ == "__main__":
    cases = [
        b'null', b'true', b'false', b'[]', b'{}', b'[1,2,3]', b'{"a":1,"b":[true,null]}',
        b'"hi"', b'  1  ', b'-0', b'007', b'1.2.3', b'1e400', b'[1]xyz', b'0.3',
        b'0.30000000000000004', b'{"a":1,"a":2}', b'"\\u00e9"', b'"\\ud83d\\ude00"',
        b'"a\\u0000b"', b'"\\uZZZZ"', b'"a\x01b"', b'1e21', b'100', b'1e2', b'1.0e2',
        b'-1.5e-3', b'123456789012345678901234567890',
    ]
    for c in cases:
        (oe, oo), (le, lo) = compare(c)
        same = "OK  " if (oe, oo) == (le, lo) else "DIFF"
        print(f'{same} {c.decode("utf-8","backslashreplace"):32s} '
              f'oracle[{oe}]={oo.decode("utf-8","backslashreplace"):26s} '
              f'lean[{le}]={lo.decode("utf-8","backslashreplace")}')
