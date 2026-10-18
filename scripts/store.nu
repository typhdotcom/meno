use ../deps/droste/droste.nu

def checked [command: list<string>] {
    let result = ^($command | first) ...($command | skip 1) | complete
    if $result.exit_code != 0 { error make {msg: ($result.stdout + $result.stderr)} }
    $result.stdout | str trim
}

# Resolve each project's search path in its own directory: their libraries
# are independent, and the exporter needs Meno's path only while importing it.
def lean-path [] {
    checked [lake env printenv LEAN_PATH] | split row (char esep)
        | each {|p| $p | path expand } | str join (char esep)
}

def --env prepare [] {
    cd ($env.FILE_PWD | path dirname)
    let state = $env.XDG_STATE_HOME? | default ($nu.home-dir | path join .local state) | path join perkeep-math
    $env.CAMLI_CONFIG_DIR = $state | path join config
    $env.PK_SERVER = "http://localhost:3180"
    $env.MENO_ANCHOR = $state | path join anchors meno
    print --stderr "Building Meno..."
    checked [lake build] | ignore
    $env.MENO_LEAN_PATH = lean-path
    $env.DROSTE_BIN = $env.PWD | path join deps droste .lake build bin droste
    $env.LEAN_PATH = do {
        cd deps/droste
        print --stderr "Building droste..."
        checked [lake build droste] | ignore
        lean-path
    }
}

def anchor [] {
    if not ($env.MENO_ANCHOR | path exists) {
        error make {msg: "No meno snapshot in the global store; run `nu tasks.nu snapshot`."}
    }
    open $env.MENO_ANCHOR | str trim
}

def export-stream [file: path] {
    print --stderr "Exporting Meno..."
    with-env {LEAN_PATH: $env.MENO_LEAN_PATH} {
        ^$env.DROSTE_BIN export Meno Meno o> $file
        if $env.LAST_EXIT_CODE != 0 { error make {msg: "Meno export failed."} }
    }
}

def tip [file: path] {
    checked [uv run deps/droste/scripts/tip.py $file]
}

def main [] { error make {msg: "Use snapshot or project NAME."} }

def "main snapshot" [] {
    prepare
    let stream = mktemp -t meno.XXXXXX
    let result = try {
        export-stream $stream
        print --stderr "Uploading to the global math store..."
        let uploaded = open --raw $stream | ^uv run deps/droste/scripts/put.py | complete
        if $uploaded.exit_code != 0 { error make {msg: $uploaded.stderr} }
        let ref = $uploaded.stdout | str trim
        if $ref != (tip $stream) { error make {msg: "Uploaded root differs from exported snapshot."} }
        if not ($env.MENO_ANCHOR | path exists) {
            mkdir ($env.MENO_ANCHOR | path dirname)
            checked [pk-put permanode -title meno] | lines | first | save $env.MENO_ANCHOR
        }
        checked [pk-put attr (anchor) camliContent $ref] | ignore
        $ref
    } catch {|err|
        rm -f $stream
        error make {msg: $err.msg}
    }
    rm -f $stream
    $result
}

def "main project" [name: string] {
    prepare
    let exe = [$env.DROSTE_BIN]
    if (droste projectors $exe | where name == $name | is-empty) {
        error make {msg: $"Unknown projector: ($name)"}
    }
    let ref = droste attrs (anchor) | get camliContent | first
    let held = droste held (droste runs $exe $name) $ref
    if $held != null { return $held }
    let stream = mktemp -t meno.XXXXXX
    let result = try {
        droste project $exe $name $ref {
            export-stream $stream
            if (tip $stream) != $ref {
                error make {msg: "The build differs from the stored snapshot; run `nu tasks.nu snapshot`."}
            }
            $stream
        }
    } catch {|err|
        rm -f $stream
        error make {msg: $err.msg}
    }
    rm -f $stream
    $result
}
