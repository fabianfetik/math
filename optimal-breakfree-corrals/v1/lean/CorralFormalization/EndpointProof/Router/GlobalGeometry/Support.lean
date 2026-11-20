import CorralFormalization.EndpointProof.Router.EndpointRouting

/-! # Raw numerical support certificates for installed router tables

The fields below concern only fixed coordinate lists and ports.  In particular,
they do not assume simplicity, rainbowness, a setting, or a routing conclusion.
-/
namespace EndpointRouter
open EndpointFactor
open scoped Classical
noncomputable section
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : Type v} [AddCommGroup G]

namespace MatchingLayer

/-- Exactly the local units actually used by one installed matching layer. -/
abbrev Unit (L : MatchingLayer α) :=
  Sum {e : α × α // e ∈ L.edges} {i : α // L.Isolated i}

instance (L : MatchingLayer α) : Fintype L.Unit :=
  inferInstanceAs (Fintype (Sum {e : α × α // e ∈ L.edges} {i : α // L.Isolated i}))

instance (L : MatchingLayer α) : DecidableEq L.Unit := Classical.decEq _

/-- The unit containing a track, without making a switch-setting choice. -/
def unitOf (L : MatchingLayer α) (i : α) : L.Unit :=
  if hi : L.Isolated i then .inr ⟨i, hi⟩
  else .inl ⟨L.incidentEdge i hi, L.incidentEdge_mem i hi⟩

end MatchingLayer

namespace LayerGeometry
variable {L : MatchingLayer α} {input output : α → G}

/-- The actual combined numerical support; the input/output ports are excluded. -/
def unitSupport (D : LayerGeometry L input output) : L.Unit → Finset G
  | .inl e => ((D.exchange e).interior ++ (D.exchange e).colors).toFinset
  | .inr i => ((D.idle i).interior ++ (D.idle i).colors).toFinset

end LayerGeometry

/-- A single injective index for all three ordered port sets. -/
def routerPort {n : ℕ} (input intermediate output : Fin n → G) (p : Fin 3 × Fin n) : G :=
  if p.1 = 0 then input p.2 else if p.1 = 1 then intermediate p.2 else output p.2

omit [AddCommGroup G] in
@[simp] theorem routerPort_input {n : ℕ} (x m z : Fin n → G) (i : Fin n) :
    routerPort x m z (0, i) = x i := rfl
omit [AddCommGroup G] in
@[simp] theorem routerPort_intermediate {n : ℕ} (x m z : Fin n → G) (i : Fin n) :
    routerPort x m z (1, i) = m i := rfl
omit [AddCommGroup G] in
@[simp] theorem routerPort_output {n : ℕ} (x m z : Fin n → G) (i : Fin n) :
    routerPort x m z (2, i) = z i := rfl

def routerPorts {n : ℕ} (input intermediate output : Fin n → G) : Finset G :=
  Finset.univ.image (routerPort input intermediate output)

def twoLayerUnitSupport {n : ℕ} {L₁ L₂ : MatchingLayer (Fin n)}
    {input intermediate output : Fin n → G}
    (first : LayerGeometry L₁ input intermediate)
    (second : LayerGeometry L₂ intermediate output) : Sum L₁.Unit L₂.Unit → Finset G
  | .inl u => first.unitSupport u
  | .inr u => second.unitSupport u

/-- The primitive installer's raw output, plus the independently selected ports.
No field mentions a path or a switch setting. -/
structure TwoLayerSupport {n : ℕ} {L₁ L₂ : MatchingLayer (Fin n)}
    {input intermediate output : Fin n → G}
    (first : LayerGeometry L₁ input intermediate)
    (second : LayerGeometry L₂ intermediate output) : Prop where
  ports_injective : Function.Injective (routerPort input intermediate output)
  disjoint : Pairwise (fun u v : Sum L₁.Unit L₂.Unit =>
    Disjoint (twoLayerUnitSupport first second u) (twoLayerUnitSupport first second v))
  avoid_ports : ∀ u, Disjoint (twoLayerUnitSupport first second u)
    (routerPorts input intermediate output)

end
end EndpointRouter
