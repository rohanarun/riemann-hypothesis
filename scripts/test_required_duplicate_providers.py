import shutil
import subprocess
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
from unittest.mock import patch

import required_duplicate_providers as duplicates
from partition_bundles import PUBLIC, Source, git


class RestoredProviderTests(unittest.TestCase):
    def setUp(self):
        directory = TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        self.work = Path(directory.name)
        self.repo = self.work / "repo"
        subprocess.run(["git", "init", "--quiet", str(self.repo)], check=True)
        (self.repo / "src").mkdir()
        self.original = {"First": Source(), "Second": Source()}
        self.statement = "theorem oldPublic : True := True.intro"
        self.code = "module\n\n@[expose] public section\n\n"
        self.caller = "\nexample : True := oldPublic\n"
        self.origins = {}
        for member in self.original:
            (self.repo / "src" / (member + ".lean")).write_text(self.code + self.statement + "\n" + self.caller)
            origin = duplicates.Origin("oldPublic", member, member, "oldPublic", True, "", (4, 0, 4, len(self.statement)))
            self.origins[member] = [origin]
        self.run_git("add", "src")
        self.historical = self.run_git("write-tree")

    def run_git(self, *args):
        return subprocess.check_output(git(self.repo, *args), text=True).strip()

    def prepare(self, mode=None):
        code = self.code
        if mode is not None:
            edge = "public import First" if mode == PUBLIC else "import First"
            code = code.replace("module\n", "module\n" + edge + "\n")
        (self.repo / "src/Second.lean").write_text(code + self.caller.lstrip("\n"))
        self.run_git("add", "src/Second.lean")
        staged = self.run_git("write-tree")
        members = {n: [n] for n in self.original}
        graph = {"First": [], "Second": [] if mode is None else ["First"]}
        modes = {"First": {}, "Second": {} if mode is None else {"First": mode}}
        return staged, SimpleNamespace(members=members, graph=graph, modes=modes,
                                       location={n: n for n in members})

    def restore(self, tree, plan):
        with patch.object(duplicates, "DECLARATION_SOURCE", self.historical), \
                patch.object(duplicates, "BEFORE_DUPLICATE_CLEANUP", self.historical):
            return duplicates.restore_providers(self.repo, tree, self.original, plan, self.origins, self.work)

    def test_lost_public_theorem_is_restored(self):
        tree, plan = self.prepare()
        self.assertEqual([x.member for x in self.restore(tree, plan)], ["Second"])
        self.assertEqual(self.run_git("write-tree"), self.historical)
        if shutil.which("lean"):
            for ref, succeeds in [(tree, False), (self.historical, True)]:
                check = self.work / "Sample.lean"
                check.write_text(self.run_git("show", ref + ":src/Second.lean") + "\n#check @oldPublic\n")
                result = subprocess.run(["lean", "-j1", check.name], cwd=self.work, capture_output=True, text=True)
                self.assertEqual(result.returncode == 0, succeeds, result.stdout + result.stderr)
                if not succeeds:
                    self.assertIn("Unknown identifier `oldPublic`", result.stdout)

    def test_existing_public_provider_is_sufficient(self):
        tree, plan = self.prepare(PUBLIC)
        self.assertEqual(self.restore(tree, plan), [])
        self.assertEqual(self.run_git("write-tree"), tree)

    def test_full_arguments_work_with_either_original_plicity(self):
        path = self.work / "uses.tsv"
        path.write_text("First\tFirst\toldPublic trivial\toldPublic True trivial\n")
        current = self.code + "theorem myProof : True := oldPublic True trivial\n"
        (self.repo / "src/First.lean").write_text(current)
        self.run_git("add", "src/First.lean")
        stage = self.run_git("write-tree")
        duplicates.retain_calling_conventions(self.repo, stage, path)
        corrected = self.run_git("write-tree")
        self.assertIn("@oldPublic True trivial", self.run_git("show", corrected + ":src/First.lean"))
        duplicates.retain_calling_conventions(self.repo, corrected, path)
        self.assertEqual(self.run_git("write-tree"), corrected)

    def test_restored_declaration_keeps_the_verified_author_qualification(self):
        data = self.work / "qualifications.tsv"
        data.write_text("First\toldPublic\tTrue\t_root_.True\n")
        file = self.repo / "src/First.lean"
        qualified = file.read_text().replace(": True := True.intro", ": _root_.True := True.intro")
        file.write_text(qualified)
        self.run_git("add", "src/First.lean")
        author = self.run_git("write-tree")
        self.run_git("read-tree", self.historical)
        with patch.object(duplicates, "DECLARATION_SOURCE", self.historical):
            duplicates.retain_author_qualifications(self.repo, self.historical, author, self.origins, data)
            self.assertEqual(self.run_git("write-tree"), author)
            with self.assertRaisesRegex(ValueError, "no longer matches"):
                duplicates.retain_author_qualifications(self.repo, self.historical, self.historical, self.origins, data)

    def test_commented_and_quoted_declarations_are_absent(self):
        fake = ("-- [dedup] theorem oldPublic : True := trivial\n"
                "/- nested /- comment -/\ntheorem oldPublic : True := trivial\n-/\n"
                'def documentation := r#"\ntheorem oldPublic : True := trivial\n"#\n')
        self.assertFalse(duplicates.declared(fake, "oldPublic"))
        self.assertTrue(duplicates.declared(fake + "@[simp] theorem oldPublic : True := trivial", "oldPublic"))
        self.assertFalse(duplicates.declaration_visibility("private theorem oldPublic : True := trivial", "oldPublic"))

    def test_private_import_cannot_supply_a_public_interface(self):
        tree, plan = self.prepare(0)
        with self.assertRaisesRegex(ValueError, "Only a private import supplies oldPublic"):
            self.restore(tree, plan)


if __name__ == "__main__":
    unittest.main()
