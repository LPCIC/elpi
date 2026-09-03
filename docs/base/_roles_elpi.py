"""
Custom Sphinx role :stdlib:`name` — links to the declaration of a builtin or
standard-library predicate inside ``src/builtin.elpi``, on GitHub.

Unlike coq-elpi's ``ghref`` (see coq-elpi/etc/alectryon_elpi.py, which this
is modelled on), this role never touches the network: ``src/builtin.elpi``
is a file of *this* repository, read straight off disk, and the commit it
links against is resolved with a local ``git`` call rather than the GitHub
API.

The link is pinned to the last commit that touched ``src/builtin.elpi`` (so
it stays a stable permalink even as the file is edited on ``master`` after a
given manual is published). The line numbers themselves are computed from
the working tree's current copy of the file, so if it has been regenerated
but not yet committed, the pin and the line numbers can disagree; the
short commit and a content hash of the file are embedded in the manual
(see |stdlib_pin| / |stdlib_hash| in builtins.rst) so that is visible rather
than silent.
"""

import hashlib
import os
import re
import subprocess
from functools import lru_cache

from docutils import nodes
from docutils.parsers.rst import roles

REPO_ORG = "LPCIC"
REPO_NAME = "elpi"
TARGET_PATH = "src/builtin.elpi"

# The handful of token sequences that actually precede `pred`/`func` at the
# start of a declaration line in src/builtin.elpi (checked by grepping the
# file): nothing, `builtin`, `:functional`, or `:functional :builtin`. Other
# attributes (`:index (...)`, `:nooc`, `:untyped`, ...) always sit on their
# own preceding line, so they never need to be matched here.
_DECL_RE = re.compile(
    r'^\s*(?:builtin\s+|:functional\s+(?::builtin\s+)?)?'
    r'(?:pred|func)\s+(?P<name>\S+)'
)
_NS_OPEN_RE = re.compile(r'^\s*namespace\s+(?P<name>\S+)\s*\{')
_NS_CLOSE_RE = re.compile(r'^\s*\}')

_HERE = os.path.dirname(os.path.abspath(__file__))


def _git(cwd, *args):
    return subprocess.run(
        ['git', *args], cwd=cwd, capture_output=True, text=True, check=True
    ).stdout


@lru_cache(maxsize=1)
def _repo_root():
    # Resolved from _HERE (this file's own directory), which is inside the
    # working tree whether this module runs from docs/base or from its
    # doc-build copy docs/source. Every other git call below then runs with
    # cwd=root, so TARGET_PATH (repo-root-relative) resolves correctly
    # regardless of where this module itself happens to live.
    return _git(_HERE, 'rev-parse', '--show-toplevel').strip()


@lru_cache(maxsize=1)
def _pin():
    """
    Returns (full_sha, short_hash) for src/builtin.elpi, where full_sha is
    the commit to link against (the last one that touched the file) and
    short_hash is a content fingerprint of the file as it is on disk right
    now, meant to be embedded in the manual as a human-visible freshness
    marker.
    """
    root = _repo_root()
    target = os.path.join(root, TARGET_PATH)

    full_sha = _git(root, 'log', '-1', '--format=%H', '--', TARGET_PATH).strip()
    if not full_sha:
        raise RuntimeError(f"{TARGET_PATH} has no git history")

    with open(target, 'rb') as f:
        on_disk = f.read()

    return full_sha, hashlib.sha256(on_disk).hexdigest()[:12]


@lru_cache(maxsize=1)
def _line_index():
    """{fully qualified pred/func name: 1-based line number} for every
    pred/func declaration in src/builtin.elpi, honouring `namespace .. { }`
    nesting (so a name declared inside `namespace std.map { }` is indexed
    under its full name `std.map.<name>`, not its bare in-namespace one)."""
    target = os.path.join(_repo_root(), TARGET_PATH)
    index = {}
    stack = []
    with open(target, encoding='utf-8') as f:
        for lineno, line in enumerate(f, start=1):
            m = _NS_OPEN_RE.match(line)
            if m:
                stack.append(m.group('name'))
                continue
            if _NS_CLOSE_RE.match(line):
                if stack:
                    stack.pop()
                continue
            m = _DECL_RE.match(line)
            if m:
                prefix = '.'.join(stack)
                bare = m.group('name').rstrip('.')
                full = f'{prefix}.{bare}' if prefix else bare
                # first declaration wins (relevant only for a handful of
                # `Deprecated, use ...` aliases that redeclare a name)
                index.setdefault(full, lineno)
    return index


def pinned_commit_short():
    """Public helper for conf.py / other roles: the short commit hash the
    :stdlib: role is currently pinned to."""
    full_sha, _ = _pin()
    return full_sha[:10]


def pinned_content_hash():
    """Public helper: a short content fingerprint of src/builtin.elpi as it
    is on disk right now, for embedding in the manual as a freshness
    marker."""
    _, short_hash = _pin()
    return short_hash


def pinned_file_url():
    """Public helper: the GitHub URL of src/builtin.elpi itself (no line
    anchor), at the same pinned commit every :stdlib: link uses."""
    full_sha, _ = _pin()
    return f"https://github.com/{REPO_ORG}/{REPO_NAME}/blob/{full_sha}/{TARGET_PATH}"


def stdlib_role(role, rawtext, text, lineno, inliner, options={}, content=[]):
    try:
        full_sha, _ = _pin()
    except RuntimeError as e:
        msg = inliner.reporter.error(str(e), line=lineno)
        return [inliner.problematic(rawtext, rawtext, msg)], [msg]

    target_lineno = _line_index().get(text)
    if target_lineno is None:
        msg = inliner.reporter.error(
            f"stdlib: '{text}' not found in {TARGET_PATH} "
            f"(pred/func declarations only)", line=lineno)
        return [inliner.problematic(rawtext, rawtext, msg)], [msg]

    uri = (f"https://github.com/{REPO_ORG}/{REPO_NAME}/blob/"
           f"{full_sha}/{TARGET_PATH}#L{target_lineno}")
    roles.set_classes(options)
    options.setdefault('classes', []).append('stdlib')
    literal = nodes.literal(text, text)
    node = nodes.reference(rawtext, '', literal, refuri=uri, **options)
    return [node], []


def setup(app):
    app.add_role('stdlib', stdlib_role)
    return {'version': '1.0', 'parallel_read_safe': True}
