import ZEditor.App

/-! The 2026 edition: the 1990 edition plus chosen improvements (see "Two
editions" in `README.md`). -/

def main (args : List String) : IO UInt32 :=
  ZEditor.App.run ZEditor.Impl.edition2026 "zeditor2026" args
