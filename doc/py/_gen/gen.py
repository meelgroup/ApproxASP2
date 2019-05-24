#!/usr/bin/env python3

import os
import pdoc
import clingo
import clingo.ast
import importlib.machinery
import re

def _is_public(ident_name):
    """
    Returns `True` if `ident_name` matches the export criteria for an
    identifier name.
    """
    return not ident_name.startswith("_") or ident_name.startswith("__")

pdoc._is_public = _is_public

clingo.ast.__spec__ = importlib.machinery.ModuleSpec("clingo.ast", None)

clingo.__pdoc__ = {}
clingo.__pdoc__['TruthValue.__eq__'] = """\
__eq__(self, value: any) -> bool

Equality compare two truth values using standard python conventions.
"""

pdoc.tpl_lookup.directories.insert(0, './templates')
ctx = pdoc.Context()

cmod = pdoc.Module(clingo, context=ctx)
amod = pdoc.Module(clingo.ast, supermodule=cmod, context=ctx)

cmod.doc["ast"] = amod
cmod.doc["__version__"] = pdoc.Variable("__version__", cmod, "version of the clingo module (`'{}'`)".format(clingo.__version__))
cmod.doc["Infimum"] = pdoc.Variable("Infimum", cmod, "represents a `clingo.Symbol` of type `clingo.SymbolType.Infimum`")
cmod.doc["Supremum"] = pdoc.Variable("Supremum", cmod, "represents a `clingo.Symbol` of type `clingo.SymbolType.Supremum`")
pdoc.link_inheritance(ctx)

os.makedirs("../clingo/ast", exist_ok=True)
open("../clingo/index.html", "w").write(cmod.html(external_links=True))
open("../clingo/ast/index.html", "w").write(amod.html(external_links=True))
