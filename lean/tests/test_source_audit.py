import unittest,tempfile,os
from pathlib import Path
from source_audit import lean_code,import_names,project_dependencies,fresh_lean_path,forbidden_constructs
class SourceAuditTests(unittest.TestCase):
 def test_all_project_prefixes(self):
  s='import SimplexFull.A\nimport WeakSimplexConjectureLean.Normal.Mills\npublic import SimplexUniquenessLean.StrictRectangle\n'
  self.assertEqual(len(project_dependencies(s)),3)
 def test_multiple_imports(self):
  self.assertEqual(project_dependencies('import SimplexFull.A SimplexFull.B'),['SimplexFull.A','SimplexFull.B'])
 def test_nested_comments_not_imports(self):
  s='/- import Evil.A\n/- import Evil.B -/\n-/\nimport Mathlib -- import Evil.C\n'
  self.assertEqual(import_names(s),['Mathlib'])
 def test_strings_not_imports(self):
  self.assertNotIn('sorry',lean_code('def s := "sorry\\\"admit"\n'))
 def test_inline_comment_separates_tokens(self):
  self.assertEqual(project_dependencies('import/- ok -/ SimplexFull.A'),['SimplexFull.A'])
 def test_unknown_import_rejected(self):
  with self.assertRaises(ValueError):import_names('import Unverified.Proof')
 def test_malformed_import_rejected(self):
  with self.assertRaises(ValueError):import_names('import SimplexFull.A;')
 def test_duplicate_imports(self):
  self.assertEqual(project_dependencies('import SimplexFull.A\nimport SimplexFull.A'),['SimplexFull.A'])
 def test_library_not_custom(self):
  self.assertEqual(project_dependencies('import Mathlib.Probability.Distributions.Gaussian.Multivariate\nimport Lean'),[])
 def test_unterminated_comment(self):
  with self.assertRaises(ValueError):lean_code('/- unclosed')
 def test_unterminated_string(self):
  with self.assertRaises(ValueError):lean_code('"unclosed')
 def test_remove_all_old_project_roots(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=Path(tmp);old=p/'old';lib=p/'lib';new=p/'fresh';root=p/'project'
   (old/'WeakSimplexConjectureLean').mkdir(parents=True);lib.mkdir()
   result,removed=fresh_lean_path(str(old)+os.pathsep+str(lib),new,root)
   self.assertEqual(result,os.pathsep.join([str(new.resolve()),str(lib.resolve())]))
   self.assertEqual(removed,[str(old.resolve())])
 def test_remove_live_source_build(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=Path(tmp);result,removed=fresh_lean_path(str(p/'build'),p/'fresh',p)
   self.assertEqual(result,str((p/'fresh').resolve()));self.assertEqual(len(removed),1)
 def test_remove_bare_project_compiled_modules(self):
  with tempfile.TemporaryDirectory() as tmp:
   p=Path(tmp);lib=p/'lib';new=p/'fresh';root=p/'project';lib.mkdir()
   for ext in ('.olean','.olean.private','.olean.server','.ilean'):
    old=p/('bare'+ext);old.mkdir()
    (old/('WeakSimplexConjectureLean'+ext)).write_bytes(b'')
    result,removed=fresh_lean_path(str(old)+os.pathsep+str(lib),new,root)
    self.assertEqual(result,os.pathsep.join([str(new.resolve()),str(lib.resolve())]))
    self.assertEqual(removed,[str(old.resolve())])
 def test_multiline_import_fails_closed(self):
  for header in ('import\n Mathlib.Data.Real.Basic','import\n Unverified.Proof','public import\n Mathlib'):
   with self.assertRaises(ValueError):import_names(header)
 def test_import_continuation_rejected(self):
  with self.assertRaises(ValueError):import_names('import Mathlib\n Unverified.Proof')
 def test_declaration_after_header(self):
  self.assertEqual(project_dependencies('module\npublic import SimplexFull.A\nnoncomputable section\nnamespace Demo\ndef x := 1'),['SimplexFull.A'])
 def test_kernel_bypass_rejected(self):
  self.assertEqual(forbidden_constructs('set_option debug.skipKernelTC true'),['debug.skipKernelTC'])
 def test_kernel_option_in_comment_not_flagged(self):
  self.assertEqual(forbidden_constructs('/- debug.skipKernelTC -/\ndef s := "sorry"'),[])

 def test_meta_import_fails_closed(self):
  for header in ('module\npublic meta import Lean.Meta.Basic','module\npublic meta import Unverified.Proof','meta import SimplexFull.A'):
   with self.assertRaises(ValueError):import_names(header)
if __name__=='__main__':unittest.main()
