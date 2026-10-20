# Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0
# Synthetic persisted-data controls, not physical observations or an oracle.
# Change individual hex digits without converting 64-bit words to AWK doubles.
BEGIN { FS = OFS = "\t"; digits = "0123456789abcdef" }
function bit(word, from_right, mask, wanted,    pos,n,old) {
    pos = length(word) + 1 - from_right
    n = index(digits, substr(word,pos,1)) - 1
    old = int(n / mask) % 2
    if (wanted < 0) wanted = 1 - old
    n += (wanted - old) * mask
    return substr(word,1,pos-1) substr(digits,n+1,1) substr(word,pos+1)
}
NR == 1 { print; next }
control == "af-clear" { $6 = bit($6,2,1,0) }
control == "af-set"   { $6 = bit($6,2,1,1) }
NR == 2 {
    if (control == "result")          $18 = bit($18,1,1,-1)
    else if (control == "upper-result") $18 = bit($18,9,1,-1)
    else if (control == "cf")         $6 = bit($6,1,1,-1)
    else if (control == "pf")         $6 = bit($6,1,4,-1)
    else if (control == "zf")         $6 = bit($6,2,4,-1)
    else if (control == "sf")         $6 = bit($6,2,8,-1)
    else if (control == "of")         $6 = bit($6,3,8,-1)
    else if (control == "if")         $6 = bit($6,3,2,-1)
    else if (control == "high-flag")  $6 = bit($6,6,2,-1)
    else if (control == "register")   $19 = bit($19,1,1,-1)
    else if (control == "rsp")        $22 = bit($22,1,8,-1)
    else if (control == "input")      $7 = bit($7,1,1,-1)
    else if (control == "seed-flags") $5 = bit($5,2,1,-1)
    else if (control == "window")     $4 = "48d1e9"
    else if (control == "seed-range") $3 = "8"
    else if (control == "malformed")  NF = 27
    else if (control != "af-clear" && control != "af-set") exit 2
}
{ print }
