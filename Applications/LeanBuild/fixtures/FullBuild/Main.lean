import Generated
@[extern "fixture_increment"] opaque increment : UInt32 → UInt32
def main : IO Unit := IO.println (increment generated)
