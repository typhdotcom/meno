# Sources read at a fixed commit of their repo.
const deps = [
    [name repo rev];
    [droste ~/dev/droste 9c33f5740ad54b3cef5a30f6f48a0766f41024ff]
]

def main [] {
    print "usage: nu tasks.nu <task>"
    print ""
    print "tasks:"
    print "  check    evaluate the flake and run its checks"
    print "  fmt      rewrite the tree with the flake's formatters"
    print "  deps     install the pinned droste source"
    print "  snapshot export meno to the global math store"
    print "  project NAME get or compute a stored droste projector run"
}

# Evaluate the flake and run its checks
def "main check" [] {
    nix flake check
}

# Rewrite the tree with the flake's formatters
def "main fmt" [] {
    nix fmt
}

# Write each pinned source tree into deps/<name>, without touching its repo
def "main deps" [] {
    for d in $deps {
        let repo = $d.repo | path expand
        let dest = $env.FILE_PWD | path join deps $d.name
        let stamp = $dest | path join .rev
        if ($stamp | path exists) and (open $stamp | str trim) == $d.rev { continue }
        if ($dest | path exists) { rm -r $dest }
        let files = ^jj --ignore-working-copy -R $repo file list -r $d.rev | lines
        for f in $files {
            let out = $dest | path join $f
            mkdir ($out | path dirname)
            ^jj --ignore-working-copy -R $repo file show -r $d.rev $f | save --raw $out
        }
        $d.rev | save $stamp
        print --stderr $"($d.name): ($files | length) files at ($d.rev)"
    }
}

# Install droste before loading the module used by store operations.
def store [args: list<string>] {
    main deps
    let root = $env.FILE_PWD
    let result = ^nix develop $root -c nu ($root | path join scripts store.nu) ...$args
        | tee --stderr { lines | each {|line| print --stderr $line } } | complete
    if $result.exit_code != 0 { error make {msg: "Store command failed."} }
    # Perkeep's claim receipts precede the final snapshot or run reference.
    $result.stdout | lines | last
}

def "main snapshot" [] { store [snapshot] }
def "main project" [name: string] { store [project $name] }
