def main [] {
    print "usage: nu tasks.nu <task>"
    print ""
    print "tasks:"
    print "  check    evaluate the flake and run its checks"
    print "  fmt      rewrite the tree with the flake's formatters"
}

# Evaluate the flake and run its checks
def "main check" [] {
    nix flake check
}

# Rewrite the tree with the flake's formatters
def "main fmt" [] {
    nix fmt
}
