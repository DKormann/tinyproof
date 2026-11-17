#!/usr/bin/env python3
from pathlib import Path

count = 0
for line in Path(__file__).with_name("main.ts").read_text().splitlines():
    if line.lstrip().startswith("compile"):
        break
    if line.strip():
        count += 1

print(count)
