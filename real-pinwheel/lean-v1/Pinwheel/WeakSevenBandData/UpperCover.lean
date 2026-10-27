import Pinwheel.WeakSevenBandData.CoverChunks.Upper053

namespace RealPinwheel.WeakSevenBandData

theorem upper_largest_cover_contradiction (h : Fin 6 → ℝ) (delta : ℝ)
    (ctx : UpperLargestCtx h delta)
    (hno : ∀ sid : Fin 157, ¬ UpperSourceFits sid h delta) : False :=
  upper_node_0 h delta ctx hno

end RealPinwheel.WeakSevenBandData
