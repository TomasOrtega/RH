import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinsumQuotientOfLe
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HaarProp

open HaarLevel

/- English proof (translation)
Rewrite using `[mem_perSub]`. Simplify using `only [intM_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨_, ⟨y, rfl⟩, rfl⟩`.

Introduce and unpack `⟨_, ⟨y, rfl⟩, rfl⟩`. Conclude with `⟨y, rfl⟩`.
-/
theorem mem_perSub' {K κ ι : Type} [Field K] (R : ℕ) (x : Matrix κ ι K) :
    x ∈ perSub K κ ι R ↔ ∃ y, IntM y ∧ R • y = x := by
  rw [mem_perSub]
  simp only [intM_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨_, ⟨y, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; exact ⟨y, rfl⟩

/- English proof (translation)
Use `⟨(QuotientAddGroup.congr (t.comap e.toAddMonoidHom) t e (AddSubgroup.map_comap_eq_self_of_surjective e.surjective t)).toEquiv, fun q => ?_⟩` and prove the remaining obligations. Use `set g := QuotientAddGroup.congr (t.comap e.toAddMonoidHom) t e (AddSubgroup.map_comap_eq_self_of_surjective e.surjective t)`. Establish `h2 : g q = (e q.out : B ⧸ t)` using `by conv_lhs => rw [← QuotientAddGroup.out_eq' q]`. Both sides reduce to the same expression. Establish `h3 : ((g q).out : B ⧸ t) = (e q.out : B ⧸ t)`.

Rewrite using `[QuotientAddGroup.out_eq', h2]`. Use `hφ (g q).out _ (QuotientAddGroup.eq.1 h3)` as an intermediate fact. Express the relevant statement in the definitionally equal form `_ = φ (g q).out`. Rewrite using `[← this]`. Use `congr 1`.

Normalize the expressions using the abelian group laws.
-/
theorem transport {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (t : AddSubgroup B)
    (φ : B → ℂ) (hφ : ∀ x, ∀ y ∈ t, φ (x + y) = φ x) :
    ∃ g : (A ⧸ t.comap e.toAddMonoidHom) ≃ (B ⧸ t), ∀ q, φ (e q.out) = φ (g q).out := by
  refine ⟨(QuotientAddGroup.congr (t.comap e.toAddMonoidHom) t e
    (AddSubgroup.map_comap_eq_self_of_surjective e.surjective t)).toEquiv, fun q => ?_⟩
  set g := QuotientAddGroup.congr (t.comap e.toAddMonoidHom) t e
    (AddSubgroup.map_comap_eq_self_of_surjective e.surjective t)
  have h2 : g q = (e q.out : B ⧸ t) := by
    conv_lhs => rw [← QuotientAddGroup.out_eq' q]
    rfl
  have h3 : ((g q).out : B ⧸ t) = (e q.out : B ⧸ t) := by
    rw [QuotientAddGroup.out_eq', h2]
  have := hφ (g q).out _ (QuotientAddGroup.eq.1 h3)
  change _ = φ (g q).out
  rw [← this]; congr 1; abel

variable {K K' κ ι κ' ι' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
  [Fintype κ] [Fintype ι] [Fintype κ'] [Fintype ι']

/- English proof (translation)
Use `set d := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) with hdd`. Set `t : ℕ → AddSubgroup (Matrix κ ι K)` to `fun R => (perSub K' κ' ι' R).comap e.toAddMonoidHom`. Establish `ht : ∀ R x, x ∈ t R ↔ ∃ y, IntM y ∧ R • y = e x` using `fun R x => mem_perSub' R (e x)`. Establish `hle : ∀ R, perSub K κ ι (R * D) ≤ t R`. Introduce `R x hx`.

Take `⟨y, hy, rfl⟩` from `(mem_perSub' _ _).1 hx`. Conclude with `(ht _ _).2 ⟨_, h1 y hy, by rw [map_nsmul, mul_smul]⟩`. Establish `hne : (perSub K κ ι D).relIndex (t 1) ≠ 0`. Establish `hle' : t (1 * (D * D')) ≤ perSub K κ ι D`. Introduce `x hx`.

Take `⟨y, hy, hxy⟩` from `(ht _ _).1 hx`. Use `(mem_perSub' _ _).2 ⟨_, h2 y hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_smul, ← map_nsmul, ← one_mul (D * D'), hxy, e.symm_apply_apply]`. Establish `h0 : (t (1 * (D * D'))).relIndex (t 1) ≠ 0`. Rewrite using `[AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective e.surjective, relIndex_perSub _ _ one_pos]`.

Check the signs of the components of the expression. Conclude with `fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hle' h)`. Establish `hsc : ∀ R, 0 < R → (perSub K κ ι (R * D)).relIndex (t R) = (perSub K κ ι D).relIndex (t 1)`. Introduce `R hR`. Establish `ha : (perSub K κ ι (R * D)).comap (nsmulAddMonoidHom R) = perSub K κ ι D`.

Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_comap, mem_perSub', nsmulAddMonoidHom_apply, mul_smul, nsmul_cancel hR]`. Establish `hb : (t 1).map (nsmulAddMonoidHom R) = t R`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_map, ht, nsmulAddMonoidHom_apply, one_smul]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, ⟨z, hz, rfl⟩, rfl⟩`. Conclude with `⟨_, hz, by rw [map_nsmul]⟩`. Introduce and unpack `⟨y, hy, hxy⟩`. Use `⟨e.symm y, ⟨y, hy, by simp⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_nsmul, hxy, e.symm_apply_apply]`. Rewrite using `[← ha, AddSubgroup.relIndex_comap, hb]`. Use `⟨((perSub K κ ι D).relIndex (t 1) : ℝ) / (D : ℝ) ^ d, by positivity, fun φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨S, hS, hψ⟩ : IsSB (fun m => φ (e m))` from `Dict.isSB_comp e.toAddMonoidHom D D' hD hD' h1 (fun x hx => by simpa using h2 _ hx) hφ`. Take `⟨R, hR, hφ⟩` from `hφ`.

Take `⟨g, hg⟩` from `transport e (perSub K' κ' ι' R) φ (periodic hφ)`. Establish `hidx : (perSub K κ ι (R * D * S)).relIndex (t R) = S ^ d * (perSub K κ ι D).relIndex (t 1)`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex _ _ _ (perSub_le (R * D) S) (hle R), hsc R hR, relIndex_perSub _ _ (by positivity)]`. Establish `hfin : (Function.support fun q : Matrix κ ι K ⧸ t R => φ (e q.out)).Finite`. Use `(finite_support hR hφ).preimage (f := g) g.injective.injOn` as an intermediate fact.

Use `this.subset fun q hq => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Function.mem_support] at hq ⊢`. Rewrite using `[← hg]` and apply the resulting hypothesis. Establish `hsum` using `finsum_quotient_of_le ((perSub_le (R * D) S).trans (hle R)) (by rw [hidx]; positivity) (fun m => φ (e m)) (fun x y hy => by rw [map_add]; exact periodic hφ _ _ hy) hfin`. Establish `hsum2 : ∑ᶠ q : Matrix κ ι K ⧸ t R, φ (e q.out) = ∑ᶠ q : Matrix κ' ι' K' ⧸ perSub K' κ' ι' R, φ q.out`.

Rewrite using `[← finsum_comp_equiv g]`. Conclude with `finsum_congr hg`. Rewrite using `[(haar_eq_haarAt _ _ _ S _ hS hψ).1, (haar_eq_haarAt _ _ _ R _ hR hφ).1, ← haarAt_mul hS hψ (S := R * D) (by positivity), mul_comm S, haarAt, haarAt, hsum, hsum2, hidx, ← hd, ← hdd]`. Establish `hS' : (S : ℂ) ≠ 0` using `by exact_mod_cast hS.ne'`. Establish `hR' : (R : ℂ) ≠ 0` using `by exact_mod_cast hR.ne'`.

Establish `hD'' : (D : ℂ) ≠ 0` using `by exact_mod_cast hD.ne'`. Use `push_cast`. Rewrite using `[mul_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem haar_comp (e : Matrix κ ι K ≃+ Matrix κ' ι' K') (D D' : ℕ) (hD : 0 < D) (hD' : 0 < D')
    (h1 : ∀ x, IntM x → IntM (D • e x)) (h2 : ∀ x, IntM x → IntM (D' • e.symm x))
    (hd : Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) =
      Module.finrank ℚ K' * (Fintype.card κ' * Fintype.card ι')) :
    ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix κ' ι' K' → ℂ, IsSB φ → haar (fun m => φ (e m)) = c * haar φ := by
  set d := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι) with hdd
  let t : ℕ → AddSubgroup (Matrix κ ι K) := fun R => (perSub K' κ' ι' R).comap e.toAddMonoidHom
  have ht : ∀ R x, x ∈ t R ↔ ∃ y, IntM y ∧ R • y = e x := fun R x => mem_perSub' R (e x)
  have hle : ∀ R, perSub K κ ι (R * D) ≤ t R := by
    intro R x hx
    obtain ⟨y, hy, rfl⟩ := (mem_perSub' _ _).1 hx
    exact (ht _ _).2 ⟨_, h1 y hy, by rw [map_nsmul, mul_smul]⟩
  have hne : (perSub K κ ι D).relIndex (t 1) ≠ 0 := by
    have hle' : t (1 * (D * D')) ≤ perSub K κ ι D := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := (ht _ _).1 hx
      refine (mem_perSub' _ _).2 ⟨_, h2 y hy, ?_⟩
      rw [← mul_smul, ← map_nsmul, ← one_mul (D * D'), hxy, e.symm_apply_apply]
    have h0 : (t (1 * (D * D'))).relIndex (t 1) ≠ 0 := by
      rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective e.surjective,
        relIndex_perSub _ _ one_pos]
      positivity
    exact fun h => h0 (AddSubgroup.relIndex_eq_zero_of_le_left hle' h)
  have hsc : ∀ R, 0 < R → (perSub K κ ι (R * D)).relIndex (t R) =
      (perSub K κ ι D).relIndex (t 1) := by
    intro R hR
    have ha : (perSub K κ ι (R * D)).comap (nsmulAddMonoidHom R) = perSub K κ ι D := by
      ext x
      simp only [AddSubgroup.mem_comap, mem_perSub', nsmulAddMonoidHom_apply, mul_smul,
        nsmul_cancel hR]
    have hb : (t 1).map (nsmulAddMonoidHom R) = t R := by
      ext x
      simp only [AddSubgroup.mem_map, ht, nsmulAddMonoidHom_apply, one_smul]
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨_, hz, by rw [map_nsmul]⟩
      · rintro ⟨y, hy, hxy⟩
        refine ⟨e.symm y, ⟨y, hy, by simp⟩, ?_⟩
        rw [← map_nsmul, hxy, e.symm_apply_apply]
    rw [← ha, AddSubgroup.relIndex_comap, hb]
  refine ⟨((perSub K κ ι D).relIndex (t 1) : ℝ) / (D : ℝ) ^ d, by positivity, fun φ hφ => ?_⟩
  obtain ⟨S, hS, hψ⟩ : IsSB (fun m => φ (e m)) :=
    Dict.isSB_comp e.toAddMonoidHom D D' hD hD' h1 (fun x hx => by simpa using h2 _ hx) hφ
  obtain ⟨R, hR, hφ⟩ := hφ
  obtain ⟨g, hg⟩ := transport e (perSub K' κ' ι' R) φ (periodic hφ)
  have hidx : (perSub K κ ι (R * D * S)).relIndex (t R) =
      S ^ d * (perSub K κ ι D).relIndex (t 1) := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (perSub_le (R * D) S) (hle R), hsc R hR,
      relIndex_perSub _ _ (by positivity)]
  have hfin : (Function.support fun q : Matrix κ ι K ⧸ t R => φ (e q.out)).Finite := by
    have := (finite_support hR hφ).preimage (f := g) g.injective.injOn
    refine this.subset fun q hq => ?_
    simp only [Set.mem_preimage, Function.mem_support] at hq ⊢
    rwa [← hg]
  have hsum := finsum_quotient_of_le ((perSub_le (R * D) S).trans (hle R))
    (by rw [hidx]; positivity) (fun m => φ (e m))
    (fun x y hy => by rw [map_add]; exact periodic hφ _ _ hy) hfin
  have hsum2 : ∑ᶠ q : Matrix κ ι K ⧸ t R, φ (e q.out) =
      ∑ᶠ q : Matrix κ' ι' K' ⧸ perSub K' κ' ι' R, φ q.out := by
    rw [← finsum_comp_equiv g]
    exact finsum_congr hg
  rw [(haar_eq_haarAt _ _ _ S _ hS hψ).1, (haar_eq_haarAt _ _ _ R _ hR hφ).1,
    ← haarAt_mul hS hψ (S := R * D) (by positivity), mul_comm S, haarAt, haarAt, hsum, hsum2, hidx,
    ← hd, ← hdd]
  have hS' : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hD'' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  push_cast
  rw [mul_pow, mul_pow]
  field_simp

end GlobalTheory.SW.HaarProp

/- English proof (translation)
Introduce `E _ _ _ n N`. Take `⟨D, hD, h⟩` from `Dict.exists_den_ofQ (E := E) (n := n) (N := N)`. Take `⟨D', hD', h'⟩` from `Dict.exists_den_symm (E := E) (n := n) (N := N)`. Conclude with `HaarProp.haar_comp (Dict.ofQEquiv E n N) D D' hD hD' h h' (by simp; ring)`.
-/
theorem GlobalTheory.SW.haar_ofQ_proportional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → haar (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) = c * haar φ := by
  intro E _ _ _ n N
  obtain ⟨D, hD, h⟩ := Dict.exists_den_ofQ (E := E) (n := n) (N := N)
  obtain ⟨D', hD', h'⟩ := Dict.exists_den_symm (E := E) (n := n) (N := N)
  exact HaarProp.haar_comp (Dict.ofQEquiv E n N) D D' hD hD' h h' (by simp; ring)
