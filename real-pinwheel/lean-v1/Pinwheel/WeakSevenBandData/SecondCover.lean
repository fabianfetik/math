import Pinwheel.WeakSevenBandData.CoverChunks.Second002

namespace RealPinwheel.WeakSevenBandData

theorem second_cover_contradiction (h : Fin 6 → ℝ) (delta : ℝ)
    (ctx : SecondCtx h delta)
    (hno : ∀ sid : Fin 15, ¬ SecondSourceFits sid h delta) : False :=
  second_node_0 h delta ctx hno

end RealPinwheel.WeakSevenBandData
