"""
File: scripts/python/_utils/__init__.py

Description:
  Utility modules for functional programming and mathematical pipeline operations.

  This package provides the mathematical foundations for the documentation build pipeline,
  including immutable data structures, functional error handling, and pure transformations.

Provenance:
  Copyright 2025-2026 William DeMeo and Contributors (agda-native-air);
  Copyright 2018-2026 The agda-algebras development team.  Licensed
  under the Apache License, Version 2.0.

  Adapted from formalverification/agda-native-air/ at SHA 664b919.
  Copied into lean2agda from ualib/agda-algebras, scripts/python/_utils/,
  at commit ee830be, unchanged.  See NOTICE.
"""

from .pipeline_types import (
    # Functional error handling
    Result,
    PipelineError,
    ErrorType,

    # Pipeline state management
    PipelineState,
    PipelineStatistics,
    ProcessedFile,
    FileMetadata,
    ProcessingStage,

    # Command execution
    CommandResult,

    # Function types
    ProcessingFunction,
    FileTransformer,
    PipelineStage,

    # Utility functions
    sequence_results,
    collect_errors,
)

__all__ = [
    # Error handling
    "Result",
    "PipelineError",
    "ErrorType",

    # State management
    "PipelineState",
    "PipelineStatistics",
    "ProcessedFile",
    "FileMetadata",
    "ProcessingStage",

    # Command execution
    "CommandResult",

    # Function types
    "ProcessingFunction",
    "FileTransformer",
    "PipelineStage",

    # Utilities
    "sequence_results",
    "collect_errors",
]
