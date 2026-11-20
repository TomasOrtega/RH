import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ToCellSurj

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

def Ak : Subgroup K := S.subgroupOf K

def πk (hD : Data W S N' K π) : K →* Ak S K where
  toFun k := ⟨⟨π k, hD.kπ k k.2⟩, by show π k ∈ S; exact hD.mem k⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem πk_id (hD : Data W S N' K π) (a : Ak S K) : πk W S N' K π hD a = a := by
  obtain ⟨⟨x, hxK⟩, hxS⟩ := a
  have hxS' : x ∈ S := by simpa [Ak, Subgroup.mem_subgroupOf] using hxS
  ext
  simp [πk, hD.id x hxS']

def Hk : Subgroup K := (Hs W K g).subgroupOf K

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Move the embeddings inside the algebraic operations. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem cellRel_iff (hD : Data W S N' K π) (k₁ k₂ : K) :
    (cellRel W N' K g).r (toCell W S N' K π g hD k₁) (toCell W S N' K π g hD k₂) ↔
      ∃ n ∈ (πk W S N' K π hD).ker, ∃ h ∈ Hk W K g, k₂ = n * k₁ * h := by
  show cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ ∈ K ⊓ N' ↔ _
  constructor
  · rintro ⟨hK, hN⟩
    set x := cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ with hx
    refine ⟨⟨x, hK⟩, ?_, k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂, ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      have h1 : π x = 1 := (hD.ker x).1 hN
      ext
      simp [πk, h1]
    · rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf]
      refine ⟨(k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂).2, ?_⟩
      rw [MulAction.mem_stabilizer_iff]
      have e2 := cell_smul W S N' K π hD ((k₂ : G) * g)
      have e1 := cell_smul W S N' K π hD ((k₁ : G) * g)
      calc ((k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂ : K) : G) • g • W
          = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • ((cell π ((k₂ : G) * g))⁻¹ • (((k₂ : G) * g) • W)) := by
            rw [← mul_smul, ← mul_smul, ← mul_smul]
            congr 1
            push_cast
            rw [hx]
            group
        _ = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • W := by rw [← e2, inv_smul_smul]
        _ = g • W := by rw [mul_smul, e1, ← mul_smul]; simp
    · ext
      push_cast
      group
  · rintro ⟨n, hn, h, hh, rfl⟩
    have hπn : π (n : G) = 1 := by
      rw [MonoidHom.mem_ker] at hn
      have := congrArg (fun a : Ak S K => ((a : K) : G)) hn
      simpa [πk] using this
    have hh' : (h : G) • g • W = g • W := by
      rw [Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf] at hh
      exact hh.2
    have hs : g⁻¹ * (h : G) * g ∈ S := by
      rw [← hD.stab]
      rw [mul_smul, mul_smul, hh', ← mul_smul]
      simp
    have key : cell π (((n * k₁ * h : K) : G) * g) = (n : G) * cell π ((k₁ : G) * g) := by
      have e : ((n * k₁ * h : K) : G) * g = (n : G) * ((k₁ : G) * g) * (g⁻¹ * (h : G) * g) := by
        push_cast
        group
      simp only [cell]
      rw [e, map_mul, map_mul, hπn, hD.id _ hs]
      group
    rw [key, mul_inv_cancel_right]
    exact ⟨n.2, (hD.ker n).2 hπn⟩

end Formalism.L2.SG.Pf.CountAb
