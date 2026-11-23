"""One planner-only check: source-pinned lease is on the approved open PR."""
import json,os,urllib.request
import rpc


def approved_ancestor(snapshot,fetch):
    policy=rpc.proof_policy()
    if policy.get('approval_mode')!='ancestor-of-open-pr':return
    rpc.snapshot_identity(snapshot,rpc.PROOF_OPERATION)
    pr=fetch('pulls/'+str(policy['pr_number']))
    rpc.require(pr.get('state')=='open'and pr.get('base',{}).get('ref')=='main','approved PR must remain open against main')
    rpc.require(pr.get('base',{}).get('repo',{}).get('full_name')=='leanprover-community/riemann-hypothesis','foreign PR repository')
    head=pr['head']['sha']
    rpc.require(len(head)==40 and all(c in '0123456789abcdef'for c in head),'invalid approved PR head')
    if head!=snapshot['git_commit']:
        comparison=fetch('compare/'+snapshot['git_commit']+'...'+head)
        rpc.require(comparison.get('status')in('ahead','identical')and comparison.get('merge_base_commit',{}).get('sha')==snapshot['git_commit'],'lease source is not an ancestor of approved PR')


def check(snapshot):
    def fetch(path):
        headers={'Accept':'application/vnd.github+json','User-Agent':'rh-proof-lease-planner'}
        if os.environ.get('GH_TOKEN'):headers['Authorization']='Bearer '+os.environ['GH_TOKEN']
        request=urllib.request.Request('https://api.github.com/repos/leanprover-community/riemann-hypothesis/'+path,headers=headers)
        with urllib.request.urlopen(request,timeout=30)as response:return json.load(response)
    approved_ancestor(snapshot,fetch)
