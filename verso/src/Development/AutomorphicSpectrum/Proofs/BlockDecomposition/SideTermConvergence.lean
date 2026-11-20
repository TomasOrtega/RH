import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.RgEisSide

variable {G : Type} [Group G] [TopologicalSpace G]
  {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [HeckeCharacter.toIdele]`.
-/
private theorem one_toIdele_lemma (y : IdeleGroup k) :
    (((1 : HeckeCharacter k).toIdele y : Circle) : ℂ) = 1 := by
  first
  | rfl
  | simp [HeckeCharacter.toIdele]

/- English proof (translation)
Use `⟨hs.two, mul_one 1, hs.cont, hs.piK, hs.piΓ, hs.trans, hs.mem, ⟨hs.par.closed, hs.par.iwa, ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl, continuous_one.continuousOn⟩⟩, hs.ht, fun p hp => ⟨?_, (hs.val p hp).2⟩⟩` and prove the remaining obligations. Conclude with `(one_toIdele_lemma _).symm`.
-/
theorem side_one {π : G →* GL ι 𝔸[k]} {Γ K P : Subgroup G} {i : ι} {ω : HeckeCharacter k}
    {d : ι → IdeleGroup k} {c : G → ℂ} {η : G → ℝ} (hs : Side π Γ K P i ω d c η) :
    Side π Γ K P i (1 : HeckeCharacter k) d (1 : G → ℂ) η := by
  refine ⟨hs.two, mul_one 1, hs.cont, hs.piK, hs.piΓ, hs.trans, hs.mem,
    ⟨hs.par.closed, hs.par.iwa, ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl,
      continuous_one.continuousOn⟩⟩, hs.ht, fun p hp => ⟨?_, (hs.val p hp).2⟩⟩
  exact (one_toIdele_lemma _).symm

/- English proof (translation)
Unfold `GroundTheory.Global.globalZeta`. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[norm_mul, norm_mul, one_toIdele_lemma, norm_one, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k t).2, Complex.ofReal_re]`.
-/
theorem norm_globalZeta_le (F : 𝔸[k] → ℂ) (x : ℝ) :
    ‖globalZeta F (1 : HeckeCharacter k) x‖ ≤
      ∫ t : IdeleGroup k, ‖F (t : 𝔸[k])‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ∂ideleMeasure k := by
  unfold GroundTheory.Global.globalZeta
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext t
  rw [norm_mul, norm_mul, one_toIdele_lemma, norm_one, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k t).2, Complex.ofReal_re]

/- English proof (translation)
Use `show ∀ r ∉ ({i} : Set ι), ∀ c ∈ ({i} : Set ι), (h : Matrix ι ι R) r c = 0 ∧ ((h⁻¹ : GL ι R) : Matrix ι ι R) r c = 0`. Introduce `r hr c hc`. Rewrite `hc`, `hr` using `[Set.mem_singleton_iff]`. Substitute `hc` using the available equality. Prove the components needed by the constructor for the conclusion.

Use `congrFun h1 r` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Pi.single_apply, hr]`. Use `congrFun h2 r` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Pi.single_apply, hr]`.
-/
private theorem stab_lemma {R : Type} [CommRing R] (h : GL ι R) (i : ι) (a b : R)
    (h1 : (h : Matrix ι ι R).mulVec (Pi.single i 1) = a • Pi.single i 1)
    (h2 : ((h⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) = b • Pi.single i 1) :
    h ∈ stab R {i} := by
  show ∀ r ∉ ({i} : Set ι), ∀ c ∈ ({i} : Set ι),
    (h : Matrix ι ι R) r c = 0 ∧ ((h⁻¹ : GL ι R) : Matrix ι ι R) r c = 0
  intro r hr c hc
  rw [Set.mem_singleton_iff] at hc hr
  subst hc
  constructor
  · have := congrFun h1 r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hr] using this
  · have := congrFun h2 r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hr] using this

/- English proof (translation)
Establish `hX : ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) = ((↑c₁⁻¹ : R) * c₂) • ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1)`. Rewrite using `[mul_smul, ← h, smul_smul, Units.inv_mul, one_smul]`. Establish `hY : ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) = ((↑c₂⁻¹ : R) * c₁) • ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1)`. Rewrite using `[mul_smul, h, smul_smul, Units.inv_mul, one_smul]`. Apply `stab_lemma (Y * X⁻¹) i ((↑c₁⁻¹ : R) * c₂) ((↑c₂⁻¹ : R) * c₁)` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Rewrite using `[_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`.
-/
private theorem stab_lemma_2 {R : Type} [CommRing R] (X Y : GL ι R) (i : ι) (c₁ c₂ : Rˣ)
    (h : (c₁ : R) • ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      (c₂ : R) • ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1)) :
    Y * X⁻¹ ∈ stab R {i} := by
  have hX : ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      ((↑c₁⁻¹ : R) * c₂) • ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) := by
    rw [mul_smul, ← h, smul_smul, Units.inv_mul, one_smul]
  have hY : ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      ((↑c₂⁻¹ : R) * c₁) • ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) := by
    rw [mul_smul, h, smul_smul, Units.inv_mul, one_smul]
  apply stab_lemma (Y * X⁻¹) i ((↑c₁⁻¹ : R) * c₂) ((↑c₂⁻¹ : R) * c₁)
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Units.mul_inv, Matrix.one_mulVec]
  · rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

/- English proof (translation)
Unfold `PositivityTheory.RgEis.MG.vec`. Rewrite using `[_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]`.
-/
private theorem vec_mul_lemma_3 (A B : GL ι 𝔸[k]) (i : ι) :
    vec (A * B) i = ((B⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (vec A i) := by
  unfold PositivityTheory.RgEis.MG.vec
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Introduce `hEp hTest hLines hTerm`. Unfold `PositivityTheory.RgEis.MG.SideConv`. Introduce `G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hs x hx`. Unfold `PositivityTheory.RgEis.Conv`. Introduce `g`.

Establish `hs1` using `side_one hs`. Establish `hcard : (2 : ℝ) ≤ (Fintype.card ι : ℝ)` using `by exact_mod_cast hs.two`. Establish `hx1 : (1 : ℝ) < x` using `by linarith`. Take `⟨Ψ, Ψ₁, hΨ, -, -, hsph, hZ⟩` from `hTest k ι i`. Take `⟨-, hT⟩` from `hTerm G K hK k ι π Γ P i 1 d 1 η hs1`.

Take `⟨hline, -, hscale⟩` from `hT Ψ (x : ℂ)`. Take `⟨e, he⟩` from `hLines G K hK k ι π Γ P i ω d c η hs`. Take `⟨-, hconv⟩` from `hEp k ι Ψ hΨ`. Take `⟨u, hu, hub⟩` from `hconv x {(π g * dgl d)⁻¹} (max_lt hx1 hx) isCompact_singleton`. Establish `hzt : ∀ κ ∈ K, zt π d i Ψ (1 : HeckeCharacter k) (x : ℂ) κ = globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)`.

Introduce `κ hκ`. Use `show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) (1 : HeckeCharacter k) (x : ℂ) = _`. Use `congr 1`. Use function extensionality and compare the values at `t`. Conclude with `hsph t ⟨kap π d κ, hs.piK κ hκ⟩`.

Establish `hA : ∀ q : Cos P Γ, ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ = Real.exp (x * η (rep q * g)) * (‖modPow (d i) (x : ℂ)‖ * ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖)`. Introduce `q`. Take `⟨p, hp, κ, hκ, hpk⟩` from `hs.par.iwa (rep q * g)`. Establish `hη : η (p * κ) = η p`. Rewrite using `[hs.ht.left p hp κ]`.

Establish `h1 : η κ = η 1` using `by simpa using hs.ht.right 1 κ hκ`. Rewrite using `[h1, hs.ht.rat 1 (one_mem Γ) (one_mem P), add_zero]`. Rewrite using `[hpk, hline p hp κ hκ, hzt κ hκ, hη, norm_mul, norm_mul, norm_mul, norm_mul, one_toIdele_lemma, Pi.one_apply, norm_one, one_mul, one_mul, ← Complex.ofReal_mul, Complex.norm_exp_ofReal]`. Establish `hApos : 0 < ‖modPow (d i) (x : ℂ)‖ * ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖`. Use `mul_pos ?_ (norm_pos_iff.mpr (hZ x hx1))` and prove the remaining obligations.

Unfold `GroundTheory.Automorphic.GodementSection.modPow`. Rewrite using `[Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k (d i)).2]`. Conclude with `Real.rpow_pos_of_pos (IdeleGroup.ideleModule k (d i)).2 _`. Establish `hbound : ∀ q : Cos P Γ, ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ ≤ u (e q)`. Introduce `q`.

Take `⟨a, Ha⟩` from `he q`. Establish `hw : vec (π (rep q * g) * dgl d) i = (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (vec (π (rep q)) i)`. Rewrite using `[map_mul, mul_assoc, vec_mul_lemma_3]`. Rewrite using `[← hscale a, hw, ← Matrix.mulVec_smul, ← Ha]`. Conclude with `(norm_globalZeta_le (fun t => Ψ (t • (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (ratV (e q).rep))) x).trans (hub _ rfl (e q))`.

Establish `hinj : Function.Injective e`. Introduce `q₁ q₂ heq`. Take `⟨a₁, H₁⟩` from `he q₁`. Take `⟨a₂, H₂⟩` from `he q₂`. Rewrite `H₁` using `[heq]`.

Establish `key : ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₁ : 𝔸[k]ˣ) : 𝔸[k]) • (((π (rep q₁))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i 1) = ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₂ : 𝔸[k]ˣ) : 𝔸[k]) • (((π (rep q₂))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i …` using `H₁.symm.trans H₂`. Establish `hst` using `stab_lemma_2 (π (rep q₁)) (π (rep q₂)) i _ _ key`. Rewrite `hst` using `[← map_inv, ← map_mul]`. Establish `hP` using `(hs.mem _).mpr hst`. Rewrite using `[← Quotient.out_eq q₁, ← Quotient.out_eq q₂]`.

Conclude with `Quotient.sound (QuotientGroup.rightRel_apply.mpr (Subgroup.mem_subgroupOf.mpr hP))`. Use `Summable.of_nonneg_of_le (fun q => (Real.exp_pos _).le) (fun q => ?_) ((hu.comp_injective hinj).div_const (‖modPow (d i) (x : ℂ)‖ * ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖))` and prove the remaining obligations. Use `show Real.exp (x * η (rep q * g)) ≤ u (e q) / _`. Rewrite using `[le_div_iff₀ hApos, ← hA q]`. Conclude with `hbound q`.
-/
theorem sideConv : EpConv → TestSph → Lines → Term → SideConv := by
  intro hEp hTest hLines hTerm
  unfold PositivityTheory.RgEis.MG.SideConv
  intro G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hs x hx
  unfold PositivityTheory.RgEis.Conv
  intro g
  have hs1 := side_one hs
  have hcard : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hs.two
  have hx1 : (1 : ℝ) < x := by linarith
  obtain ⟨Ψ, Ψ₁, hΨ, -, -, hsph, hZ⟩ := hTest k ι i
  obtain ⟨-, hT⟩ := hTerm G K hK k ι π Γ P i 1 d 1 η hs1
  obtain ⟨hline, -, hscale⟩ := hT Ψ (x : ℂ)
  obtain ⟨e, he⟩ := hLines G K hK k ι π Γ P i ω d c η hs
  obtain ⟨-, hconv⟩ := hEp k ι Ψ hΨ
  obtain ⟨u, hu, hub⟩ := hconv x {(π g * dgl d)⁻¹} (max_lt hx1 hx) isCompact_singleton
  have hzt : ∀ κ ∈ K, zt π d i Ψ (1 : HeckeCharacter k) (x : ℂ) κ =
      globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ) := by
    intro κ hκ
    show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) (1 : HeckeCharacter k) (x : ℂ) = _
    congr 1
    funext t
    exact hsph t ⟨kap π d κ, hs.piK κ hκ⟩
  have hA : ∀ q : Cos P Γ,
      ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ =
        Real.exp (x * η (rep q * g)) * (‖modPow (d i) (x : ℂ)‖ *
          ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖) := by
    intro q
    obtain ⟨p, hp, κ, hκ, hpk⟩ := hs.par.iwa (rep q * g)
    have hη : η (p * κ) = η p := by
      rw [hs.ht.left p hp κ]
      have h1 : η κ = η 1 := by simpa using hs.ht.right 1 κ hκ
      rw [h1, hs.ht.rat 1 (one_mem Γ) (one_mem P), add_zero]
    rw [hpk, hline p hp κ hκ, hzt κ hκ, hη, norm_mul, norm_mul, norm_mul, norm_mul,
      one_toIdele_lemma, Pi.one_apply, norm_one, one_mul, one_mul, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal]
  have hApos : 0 < ‖modPow (d i) (x : ℂ)‖ *
      ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖ := by
    refine mul_pos ?_ (norm_pos_iff.mpr (hZ x hx1))
    unfold GroundTheory.Automorphic.GodementSection.modPow
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k (d i)).2]
    exact Real.rpow_pos_of_pos (IdeleGroup.ideleModule k (d i)).2 _
  have hbound : ∀ q : Cos P Γ,
      ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ ≤ u (e q) := by
    intro q
    obtain ⟨a, Ha⟩ := he q
    have hw : vec (π (rep q * g) * dgl d) i =
        (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (vec (π (rep q)) i) := by
      rw [map_mul, mul_assoc, vec_mul_lemma_3]
    rw [← hscale a, hw, ← Matrix.mulVec_smul, ← Ha]
    exact (norm_globalZeta_le (fun t => Ψ (t • (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) :
      Matrix ι ι 𝔸[k]).mulVec (ratV (e q).rep))) x).trans (hub _ rfl (e q))
  have hinj : Function.Injective e := by
    intro q₁ q₂ heq
    obtain ⟨a₁, H₁⟩ := he q₁
    obtain ⟨a₂, H₂⟩ := he q₂
    rw [heq] at H₁
    have key : ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₁ : 𝔸[k]ˣ) : 𝔸[k]) •
        (((π (rep q₁))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i 1) =
        ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₂ : 𝔸[k]ˣ) : 𝔸[k]) •
        (((π (rep q₂))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i 1) :=
      H₁.symm.trans H₂
    have hst := stab_lemma_2 (π (rep q₁)) (π (rep q₂)) i _ _ key
    rw [← map_inv, ← map_mul] at hst
    have hP := (hs.mem _).mpr hst
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr (Subgroup.mem_subgroupOf.mpr hP))
  refine Summable.of_nonneg_of_le (fun q => (Real.exp_pos _).le) (fun q => ?_)
    ((hu.comp_injective hinj).div_const (‖modPow (d i) (x : ℂ)‖ *
      ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖))
  show Real.exp (x * η (rep q * g)) ≤ u (e q) / _
  rw [le_div_iff₀ hApos, ← hA q]
  exact hbound q

end GlobalTheory.CompanionTheory.RgEisSide
