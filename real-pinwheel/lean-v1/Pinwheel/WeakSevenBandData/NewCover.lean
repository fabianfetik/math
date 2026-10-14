import Pinwheel.WeakSevenBandData.CoverChunks.New163

namespace RealPinwheel.WeakSevenBandData

theorem new_largest_cover_contradiction (h : Fin 6 → ℝ) (delta : ℝ)
    (ctx : NewLargestCtx h delta)
    (hno : ∀ sid : Fin 263, ¬ NewSourceFits sid h delta) : False :=
  new_node_0 h delta ctx hno

end RealPinwheel.WeakSevenBandData
