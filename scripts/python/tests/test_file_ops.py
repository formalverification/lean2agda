"""
File: scripts/python/tests/test_file_ops.py

Description:
  Tests of the helpers lean2agda added to _utils/file_ops.py: file_size
  and read_bytes, on temporary files.
"""
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from _utils.file_ops import file_size, read_bytes
from _utils.pipeline_types import ErrorType


class TestFileOps(unittest.TestCase):
    def test_read_bytes_is_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "f"
            path.write_bytes(b"a\r\nb\xc2\xab")
            self.assertEqual(read_bytes(path).unwrap(), b"a\r\nb\xc2\xab")
            self.assertEqual(file_size(path).unwrap(), 6)

    def test_missing_file(self) -> None:
        missing = Path("/nonexistent/f")
        self.assertEqual(read_bytes(missing).unwrap_err().error_type, ErrorType.FILE_NOT_FOUND)
        self.assertEqual(file_size(missing).unwrap_err().error_type, ErrorType.FILE_NOT_FOUND)


if __name__ == "__main__":
    unittest.main()
