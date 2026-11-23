"""Untrusted returned files must not redirect a post-sandbox host write."""
import json,tempfile,unittest
from pathlib import Path
from host_profile import publish_profile

class ProfilePublicationTests(unittest.TestCase):
 def test_sandbox_symlinks_cannot_overwrite_host_sentinel(self):
  with tempfile.TemporaryDirectory()as directory:
   root=Path(directory);output=root/'job';returned=output/'returned';returned.mkdir(parents=True)
   sentinel=root/'host-sentinel';sentinel.write_text('preserve host bytes')
   (returned/'host-profile.json').symlink_to(sentinel)
   (returned/'host-profile.json.tmp').symlink_to(sentinel)
   profile={'cpu_seconds':1.25,'tasks_peak':None};publish_profile(output,profile)
   self.assertEqual(sentinel.read_text(),'preserve host bytes')
   self.assertFalse((returned/'host-profile.json').is_symlink())
   self.assertEqual(json.loads((returned/'host-profile.json').read_text()),profile)
   self.assertFalse(list(output.glob('.host-profile-*')))

if __name__=='__main__':unittest.main()
