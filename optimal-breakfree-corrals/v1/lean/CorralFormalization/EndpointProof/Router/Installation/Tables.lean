import CorralFormalization.EndpointProof.Router.Installation.Indexed
import CorralFormalization.EndpointProof.Router.GlobalGeometry.Support

/-! # The installed primitives are the actual local geometry tables

Only a unit's selected concrete primitive is read. Values on unused edges and
nonisolated idle slots are irrelevant defaults. Support identities below retain
an exact link with the primitive actually returned by the greedy installer.
-/
namespace EndpointRouter
open scoped BigOperators Classical
noncomputable section
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
variable {G : Type v} [AddCommGroup G] [DecidableEq G]

namespace MatchingLayer

def unitQuery (L : MatchingLayer α) (input output : α → G) : L.Unit → Query G
  | .inl e => .exchange (input e.1.1) (input e.1.2) (output e.1.1) (output e.1.2)
  | .inr i => .idle (input i) (output i)

end MatchingLayer

private def Primitive.asSwitch : Primitive G → Switch G
  | .exchange S => S
  | .idle _ => ⟨0,0,0,0,0,0,0⟩

private def Primitive.asIdle : Primitive G → Idle G
  | .idle I => I
  | .exchange _ => ⟨0,0,0,0,0,0⟩

namespace LayerGeometry
variable {L : MatchingLayer α} {input output : α → G} {RV RC : Set G}

/-- A concrete table extracted at the exact indices used by the layer. -/
def fromPrimitives (primitive : L.Unit → Primitive G)
    (hgood : ∀ u, (primitive u).Good RV RC (L.unitQuery input output u)) :
    LayerGeometry L input output where
  exchange e := if he : e ∈ L.edges then (primitive (.inl ⟨e,he⟩)).asSwitch else ⟨0,0,0,0,0,0,0⟩
  idle i := if hi : L.Isolated i then (primitive (.inr ⟨i,hi⟩)).asIdle else ⟨0,0,0,0,0,0⟩
  exchange_ports := by
    intro e he
    have h := hgood (.inl ⟨e,he⟩)
    cases hp : primitive (.inl ⟨e,he⟩) with
    | idle I => simp [MatchingLayer.unitQuery, hp, Primitive.Good] at h
    | exchange S =>
      simp only [MatchingLayer.unitQuery,hp,Primitive.Good] at h
      simpa [he,hp,Primitive.asSwitch] using And.intro h.1 (And.intro h.2.1 (And.intro h.2.2.1 h.2.2.2.1))
  exchange_valid := by
    intro e he
    have h := hgood (.inl ⟨e,he⟩)
    cases hp : primitive (.inl ⟨e,he⟩) with
    | idle I => simp [MatchingLayer.unitQuery, hp, Primitive.Good] at h
    | exchange S =>
      simp only [MatchingLayer.unitQuery,hp,Primitive.Good] at h
      simpa [he,hp,Primitive.asSwitch] using h.2.2.2.2.1
  idle_ports := by
    intro i hi
    have h := hgood (.inr ⟨i,hi⟩)
    cases hp : primitive (.inr ⟨i,hi⟩) with
    | exchange S => simp [MatchingLayer.unitQuery, hp, Primitive.Good] at h
    | idle I =>
      simp only [MatchingLayer.unitQuery,hp,Primitive.Good] at h
      simpa [hi,hp,Primitive.asIdle] using And.intro h.1 h.2.1
  idle_valid := by
    intro i hi
    have h := hgood (.inr ⟨i,hi⟩)
    cases hp : primitive (.inr ⟨i,hi⟩) with
    | exchange S => simp [MatchingLayer.unitQuery, hp, Primitive.Good] at h
    | idle I =>
      simp only [MatchingLayer.unitQuery,hp,Primitive.Good] at h
      simpa [hi,hp,Primitive.asIdle] using h.2.2.1

/-- Equality of the complete coordinate lists, hence numerical supports,
with the installed primitive; no support is supplied separately. -/
theorem fromPrimitives_unitSupport (primitive : L.Unit → Primitive G)
    (hgood : ∀ u, (primitive u).Good RV RC (L.unitQuery input output u))
    (u : L.Unit) : (fromPrimitives primitive hgood).unitSupport u = (primitive u).support := by
  rcases u with e | i
  · have h := hgood (.inl e)
    cases hp : primitive (.inl e) with
    | idle I => simp [MatchingLayer.unitQuery,hp,Primitive.Good] at h
    | exchange S =>
      ext z
      simp [unitSupport,fromPrimitives,e.property,hp,Primitive.asSwitch,Primitive.support,Primitive.interior,Primitive.colors]
  · have h := hgood (.inr i)
    cases hp : primitive (.inr i) with
    | exchange S => simp [MatchingLayer.unitQuery,hp,Primitive.Good] at h
    | idle I =>
      ext z
      simp [unitSupport,fromPrimitives,i.property,hp,Primitive.asIdle,Primitive.support,Primitive.interior,Primitive.colors]

/-- The primitive reconstructed from a used table slot. -/
def unitPrimitive (D : LayerGeometry L input output) : L.Unit → Primitive G
  | .inl e => .exchange (D.exchange e)
  | .inr i => .idle (D.idle i)

theorem fromPrimitives_unitPrimitive (primitive : L.Unit → Primitive G)
    (hgood : ∀ u, (primitive u).Good RV RC (L.unitQuery input output u))
    (u : L.Unit) : (fromPrimitives primitive hgood).unitPrimitive u = primitive u := by
  rcases u with e | i
  · have h := hgood (.inl e)
    cases hp : primitive (.inl e) with
    | idle I => simp [MatchingLayer.unitQuery,hp,Primitive.Good] at h
    | exchange S => simp [unitPrimitive,fromPrimitives,e.property,hp,Primitive.asSwitch]
  · have h := hgood (.inr i)
    cases hp : primitive (.inr i) with
    | exchange S => simp [MatchingLayer.unitQuery,hp,Primitive.Good] at h
    | idle I => simp [unitPrimitive,fromPrimitives,i.property,hp,Primitive.asIdle]

end LayerGeometry

namespace Primitive

theorem Good.interior_mem {RV RC : Set G} {q : Query G} {P : Primitive G}
    (h : P.Good RV RC q) {z : G} (hz : z ∈ P.interior) : z ∈ RV := by
  cases q <;> cases P
  · exact h.2.2.2.1 z hz
  · exact False.elim h
  · exact False.elim h
  · exact h.2.2.2.2.2.1 z hz

theorem Good.color_mem {RV RC : Set G} {q : Query G} {P : Primitive G}
    (h : P.Good RV RC q) {z : G} (hz : z ∈ P.colors) : z ∈ RC := by
  cases q <;> cases P
  · exact h.2.2.2.2 z hz
  · exact False.elim h
  · exact False.elim h
  · exact h.2.2.2.2.2.2 z hz

end Primitive

end
end EndpointRouter
