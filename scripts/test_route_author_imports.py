from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import route_author_imports as routing
from partition_bundles import Partition, Source, git, read_graph, stage_sources


class AuthorImportTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.repo = Path(tmp.name)
        subprocess.run(["git", "init", "--quiet", "--bare", str(self.repo)], check=True)
        header = "module\n\npublic import Mathlib\n"
        block = lambda name: "-- bundled from " + name + "\nsection\nexample : True := trivial\nend\n"
        self.original = {
            "Plain": Source(["Mathlib"]), "Uses": Source(["Mathlib", "Supplier"]),
            "Other": Source(["Mathlib"]), "Supplier": Source(["Mathlib"]),
        }
        self.input = {
            "Caller": header + "public import Items\npublic import Items\n" + block("Plain") + block("Uses"),
            "Items": header + block("Other") + block("Supplier"),
        }
        stage_sources(self.repo, self.input)
        self.routes = {"Caller": {"Items": [("Uses", "Supplier")]}}
        self.pinned = self.run_git("write-tree")
        self.baseline = dict(self.input)
        self.baseline["Caller"] = self.baseline["Caller"].replace("public import Items\n", "", 1)
        stage_sources(self.repo, self.baseline)
        self.before = self.run_git("write-tree")
        stage_sources(self.repo, self.input)
        with patch.object(routing, "AUTHOR_REVISION", self.pinned), \
                patch.object(routing, "BASE_AUTHOR_REVISION", self.before):
            routing.take_imports(self.repo, self.pinned, self.routes)
        self.stripped = self.run_git("write-tree")
        self.plan = Partition(self.original, read_graph(self.repo, self.stripped), ["Supplier"], [["Supplier"]])
        expanded = {}
        for target, previous in self.plan.previous.items():
            data = routing.source(self.repo, self.stripped, previous)
            expanded[target] = self.plan.render(target, data)
        stage_sources(self.repo, expanded)
        self.rendered = self.run_git("write-tree")

    def run_git(self, *args):
        return subprocess.check_output(git(self.repo, *args), text=True).strip()

    def test_repeated_import_follows_only_the_original_consumer(self):
        routed = routing.restore_imports(self.repo, self.rendered, self.routes, self.plan, ["Supplier"], [["Supplier"]])
        uses = self.plan.location["Uses"]
        supplier = self.plan.location["Supplier"]
        self.assertEqual(routed, {uses: [supplier]})
        final = read_graph(self.repo, self.run_git("write-tree"))
        self.assertEqual(final[uses].imports.count(supplier), 2)
        self.assertNotIn(supplier, final[self.plan.location["Plain"]].imports)

    def test_removed_author_import_stays_removed(self):
        self.run_git("read-tree", self.before)
        with patch.object(routing, "AUTHOR_REVISION", self.pinned), \
                patch.object(routing, "BASE_AUTHOR_REVISION", self.before):
            self.assertEqual(routing.take_imports(self.repo, self.before, self.routes), {})
        self.assertEqual(self.run_git("write-tree"), self.before)

    def test_translated_removed_wrapper_follows_its_original_owner(self):
        with_alias = dict(self.input)
        with_alias["Caller"] = with_alias["Caller"].replace("public import Items\n", "public import GoneStatement\n", 1)
        stage_sources(self.repo, with_alias)
        author = self.run_git("write-tree")
        self.run_git("read-tree", self.pinned)
        routes = {"Caller": {"GoneStatement": [("Uses", "Supplier")]}}
        with patch.object(routing, "AUTHOR_REVISION", author), \
                patch.object(routing, "BASE_AUTHOR_REVISION", self.before):
            self.assertEqual(routing.take_imports(self.repo, self.pinned, routes, {"GoneStatement": "Items"}), routes)
        self.assertEqual(self.run_git("write-tree"), self.before)

    def test_wrong_original_consumer_cannot_gain_the_protected_provider(self):
        bad = {"Caller": {"Items": [("Plain", "Supplier")]}}
        with self.assertRaisesRegex(ValueError, "change the protected choices"):
            routing.restore_imports(self.repo, self.rendered, bad, self.plan, ["Supplier"], [["Supplier"]])


if __name__ == "__main__":
    unittest.main()
