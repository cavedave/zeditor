import ZEditor.App

/-! The 1990 edition: what the specification says, repaired only where it is
broken (see "Two editions" in `README.md`). -/

def main (args : List String) : IO UInt32 :=
  ZEditor.App.run ZEditor.Impl.edition1990 "zeditor" args
