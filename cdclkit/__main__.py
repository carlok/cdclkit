# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Carlo Perassi. Licensed under the Apache License 2.0.
"""Entry point for ``python -m cdclkit``."""

import sys

from .cli import main

if __name__ == "__main__":
    sys.exit(main())
