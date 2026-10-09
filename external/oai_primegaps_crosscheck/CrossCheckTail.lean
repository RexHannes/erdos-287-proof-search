
/-! ## Native-environment cross-check (appended after the verbatim copy of `Defs.lean`) -/

open Erdos287.SourceChain.OAIImport in
/-- The transcribed Siegel–Walfisz proposition is definitionally the external one. -/
theorem crosscheck_SW : OAISiegelWalfisz ↔ OAI.LargePrimeGaps.SiegelWalfisz := Iff.rfl

open Erdos287.SourceChain.OAIImport in
/-- The transcribed Bombieri–Vinogradov proposition is definitionally the external one. -/
theorem crosscheck_BV : OAIBombieriVinogradov ↔ OAI.LargePrimeGaps.BombieriVinogradov := Iff.rfl

open Erdos287.SourceChain.OAIImport in
theorem transcribed_SW_holds : OAISiegelWalfisz := OAI.LargePrimeGaps.siegelWalfisz

open Erdos287.SourceChain.OAIImport in
theorem transcribed_BV_holds : OAIBombieriVinogradov := OAI.LargePrimeGaps.bombieriVinogradov

#check @OAI.LargePrimeGaps.siegelWalfisz
#check @OAI.LargePrimeGaps.bombieriVinogradov
#print OAI.LargePrimeGaps.SiegelWalfisz
#print OAI.LargePrimeGaps.BombieriVinogradov
#print axioms OAI.LargePrimeGaps.siegelWalfisz
#print axioms OAI.LargePrimeGaps.bombieriVinogradov
#print axioms transcribed_SW_holds
#print axioms transcribed_BV_holds
