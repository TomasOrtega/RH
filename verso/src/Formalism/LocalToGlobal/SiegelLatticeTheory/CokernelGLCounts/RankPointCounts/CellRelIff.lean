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
Take `⟨⟨x, hxK⟩, hxS⟩` from `a`. Establish `hxS' : x ∈ S` using `by simpa [Ak, Subgroup.mem_subgroupOf] using hxS`. Use `ext`. Simplify using `[πk, hD.id x hxS']`.
-/
theorem πk_id (hD : Data W S N' K π) (a : Ak S K) : πk W S N' K π hD a = a := by
  obtain ⟨⟨x, hxK⟩, hxS⟩ := a
  have hxS' : x ∈ S := by simpa [Ak, Subgroup.mem_subgroupOf] using hxS
  ext
  simp [πk, hD.id x hxS']

def Hk : Subgroup K := (Hs W K g).subgroupOf K

/- English proof (translation)
Use `show cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ ∈ K ⊓ N' ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hK, hN⟩ set x := cell π ((k₂ : G) * g) * (cell π ((k₁ : G) * g))⁻¹ with hx`. Use `⟨⟨x, hK⟩, ?_, k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker]`.

Establish `h1 : π x = 1` using `(hD.ker x).1 hN`. Use `ext`. Simplify using `[πk, h1]`. Rewrite using `[Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf]`. Use `⟨(k₁⁻¹ * ⟨x, hK⟩⁻¹ * k₂).2, ?_⟩` and prove the remaining obligations.

Rewrite using `[MulAction.mem_stabilizer_iff]`. Establish `e2` using `cell_smul W S N' K π hD ((k₂ : G) * g)`. Establish `e1` using `cell_smul W S N' K π hD ((k₁ : G) * g)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_smul, ← mul_smul, ← mul_smul]`.

Use `congr 1`. Use `push_cast`. Rewrite using `[hx]`. Use `group`. Use `_ = ((k₁ : G)⁻¹ * cell π ((k₁ : G) * g)) • W := by rw [← e2, inv_smul_smul]`.

Use `_ = g • W := by rw [mul_smul, e1, ← mul_smul]; simp`. Use `ext`. Use `push_cast`. Use `group`. Introduce and unpack `⟨n, hn, h, hh, rfl⟩`.

Establish `hπn : π (n : G) = 1`. Rewrite `hn` using `[MonoidHom.mem_ker]`. Use `congrArg (fun a : Ak S K => ((a : K) : G)) hn` as an intermediate fact. Simplify `this` using `[πk]`. Establish `hh' : (h : G) • g • W = g • W`.

Rewrite `hh` using `[Hk, Subgroup.mem_subgroupOf, Hs, Subgroup.mem_inf]`. Conclude with `hh.2`. Establish `hs : g⁻¹ * (h : G) * g ∈ S`. Rewrite using `[← hD.stab]`. Rewrite using `[mul_smul, mul_smul, hh', ← mul_smul]`.

Simplify using the standard rewrite rules. Establish `key : cell π (((n * k₁ * h : K) : G) * g) = (n : G) * cell π ((k₁ : G) * g)`. Establish `e : ((n * k₁ * h : K) : G) * g = (n : G) * ((k₁ : G) * g) * (g⁻¹ * (h : G) * g)`. Use `push_cast`. Use `group`.

Simplify using `only [cell]`. Rewrite using `[e, map_mul, map_mul, hπn, hD.id _ hs]`. Use `group`. Rewrite using `[key, mul_inv_cancel_right]`. Conclude with `⟨n.2, (hD.ker n).2 hπn⟩`.
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
