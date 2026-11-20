import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ConstBound

/- English proof (translation)
The claim follows from `Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) X`.
-/
theorem isTorsionFree_int_of {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.IsTorsionFree (𝓞 E) X] : Module.IsTorsionFree ℤ X :=
  Module.IsTorsionFree.trans_faithfulSMul ℤ (𝓞 E) X

/- English proof (translation)
Use `Dw.fin` as an intermediate fact. Use `Dw.proj` as an intermediate fact. Establish `: Module.IsTorsionFree ℤ Dw.La` using `isTorsionFree_int_of (E := E) Dw.La`. Establish `: Module.Finite ℤ Dw.La` using `Module.Finite.trans (𝓞 E) Dw.La`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
theorem datum_free {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H) :
    Module.Free ℤ Dw.La ∧ Module.Finite ℤ Dw.La := by
  have := Dw.fin
  have := Dw.proj
  have : Module.IsTorsionFree ℤ Dw.La := isTorsionFree_int_of (E := E) Dw.La
  have : Module.Finite ℤ Dw.La := Module.Finite.trans (𝓞 E) Dw.La
  exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Take `⟨hfree, hfin⟩` from `datum_free Dw`. Establish `hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb`. Establish `h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)}` using `Ideal.subset_span rfl`. Rewrite `h1` using `[← l.prod]`. Conclude with `(Ideal.mul_le_inf.trans inf_le_left) h1`.

Establish `hle : (nsmulAddMonoidHom (α` using `Dw.La) l.M).range ≤ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).toAddSubgroup := by`. Introduce and unpack `x ⟨y, rfl⟩`. Simplify using `only [nsmulAddMonoidHom_apply, Submodule.mem_toAddSubgroup]`. Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul hM Submodule.mem_top`.

Establish `key` using `AddSubgroup.index_dvd_of_le hle`. Rewrite `key` using `[AddSubgroup.index_range_nsmul]`. Unfold `LevQ`. Conclude with `key`.
-/
theorem card_levQ_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Nat.card (LevQ Dw l) ∣ l.M ^ Module.finrank ℤ Dw.La := by
  obtain ⟨hfree, hfin⟩ := datum_free Dw
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ Ideal.span {((l.M : ℕ) : 𝓞 E)} := Ideal.subset_span rfl
    rw [← l.prod] at h1
    exact (Ideal.mul_le_inf.trans inf_le_left) h1
  have hle : (nsmulAddMonoidHom (α := Dw.La) l.M).range ≤ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).toAddSubgroup := by
    rintro x ⟨y, rfl⟩
    simp only [nsmulAddMonoidHom_apply, Submodule.mem_toAddSubgroup]
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hM Submodule.mem_top
  have key := AddSubgroup.index_dvd_of_le hle
  rw [AddSubgroup.index_range_nsmul] at key
  unfold LevQ
  exact key

/- English proof (translation)
Establish `hmem : ∀ v : Fin n → E, v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, ∃ a : 𝓞 E, (a : E) = v i`. Introduce `v`. Simplify using `only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]`. Use `set L := (Formalism.L2.Pj.stdLat E n).toAddSubgroup with hL`. Establish `hmap : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup = L.map (nsmulAddMonoidHom N)`.

Use extensionality with `x`. Simplify using `only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, nsmulAddMonoidHom_apply, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, hL]`. Simplify using `only [Nat.cast_smul_eq_nsmul]`. Set `g : (Fin n → 𝓞 E) →+ L` to `{ toFun := fun a => ⟨fun i => (a i : E), (hmem _).2 fun i => ⟨a i, rfl⟩⟩ map_zero' := by ext; simp map_add' := by intro a b; ext; simp }`. Establish `hg : Function.Bijective g`.

Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Use function extensionality and compare the values at `i`. Use `congrArg (fun v : L => (v : Fin n → E) i) hab` as an intermediate fact. Conclude with `RingOfIntegers.coe_injective this`.

Introduce and unpack `⟨v, hv⟩ choose a ha using (hmem v).1 hv`. Conclude with `⟨a, Subtype.ext (funext ha)⟩`. Set `e : (Fin n → 𝓞 E) ≃ₗ[ℤ] L` to `(AddEquiv.ofBijective g hg).toIntLinearEquiv`. Establish `: Module.Free ℤ L` using `Module.Free.of_equiv e`. Establish `: Module.Finite ℤ L` using `Module.Finite.equiv e`.

Establish `hrank : Module.finrank ℤ L = Module.finrank ℚ E * n`. Rewrite using `[← e.finrank_eq, Module.finrank_pi_fintype]`. Simplify using `[NumberField.RingOfIntegers.rank, mul_comm]`. Rewrite using `[hmap, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range, AddSubgroup.index_range_nsmul, hrank]`.
-/
private theorem relIndex_span_smul_stdLat {E : Type} [Field E] [NumberField E] {n : ℕ} (N : ℕ) :
    (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup.relIndex
      (Formalism.L2.Pj.stdLat E n).toAddSubgroup = N ^ (Module.finrank ℚ E * n) := by
  have hmem : ∀ v : Fin n → E, v ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, ∃ a : 𝓞 E, (a : E) = v i := by
    intro v
    simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  set L := (Formalism.L2.Pj.stdLat E n).toAddSubgroup with hL
  have hmap : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup =
      L.map (nsmulAddMonoidHom N) := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, nsmulAddMonoidHom_apply,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, hL]
    simp only [Nat.cast_smul_eq_nsmul]
  let g : (Fin n → 𝓞 E) →+ L :=
    { toFun := fun a => ⟨fun i => (a i : E), (hmem _).2 fun i => ⟨a i, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := by intro a b; ext; simp }
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      funext i
      have := congrArg (fun v : L => (v : Fin n → E) i) hab
      exact RingOfIntegers.coe_injective this
    · rintro ⟨v, hv⟩
      choose a ha using (hmem v).1 hv
      exact ⟨a, Subtype.ext (funext ha)⟩
  let e : (Fin n → 𝓞 E) ≃ₗ[ℤ] L := (AddEquiv.ofBijective g hg).toIntLinearEquiv
  have : Module.Free ℤ L := Module.Free.of_equiv e
  have : Module.Finite ℤ L := Module.Finite.equiv e
  have hrank : Module.finrank ℤ L = Module.finrank ℚ E * n := by
    rw [← e.finrank_eq, Module.finrank_pi_fintype]
    simp [NumberField.RingOfIntegers.rank, mul_comm]
  rw [hmap, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range,
    AddSubgroup.index_range_nsmul, hrank]

/- English proof (translation)
Establish `hHK : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup` using `fun x hx => h hx`. Establish `hKL : Λ.Ln.toAddSubgroup ≤ (Formalism.L2.Pj.stdLat E n).toAddSubgroup` using `fun x hx => (inf_le_right : Λ.La ⊓ Formalism.L2.Pj.stdLat E n ≤ _) hx`. Rewrite using `[← relIndex_span_smul_stdLat N]`. Conclude with `Dvd.intro _ (AddSubgroup.relIndex_mul_relIndex _ _ _ hHK hKL)`.
-/
theorem relIndex_dvd {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) (N : ℕ) (hN : 0 < N)
    (h : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ.Ln) :
    (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup.relIndex Λ.Ln.toAddSubgroup ∣ N ^ (Module.finrank ℚ E * n) := by
  have hHK : (Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n).toAddSubgroup ≤ Λ.Ln.toAddSubgroup :=
    fun x hx => h hx
  have hKL : Λ.Ln.toAddSubgroup ≤ (Formalism.L2.Pj.stdLat E n).toAddSubgroup :=
    fun x hx => (inf_le_right : Λ.La ⊓ Formalism.L2.Pj.stdLat E n ≤ _) hx
  rw [← relIndex_span_smul_stdLat N]
  exact Dvd.intro _ (AddSubgroup.relIndex_mul_relIndex _ _ _ hHK hKL)

/- English proof (translation)
Establish `key` using `relIndex_dvd Λ N hN h`. Rewrite `key` using `[AddSubgroup.relIndex]`. Rewrite using `[Formalism.L2.Pj.GenLat.mIdx, pow_mul]`. Conclude with `pow_dvd_pow_of_dvd key r`.
-/
theorem mIdx_dvd {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) (N r : ℕ) (hN : 0 < N)
    (h : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ.Ln) : Λ.mIdx N r ∣ N ^ (Module.finrank ℚ E * n * r) := by
  have key := relIndex_dvd Λ N hN h
  rw [AddSubgroup.relIndex] at key
  rw [Formalism.L2.Pj.GenLat.mIdx, pow_mul]
  exact pow_dvd_pow_of_dvd key r

/- English proof (translation)
Introduce `E _ _ _ H Dw n d M p hp hM`. Establish `hp1 : p ≠ 1` using `hp.one_lt.ne'`. Establish `hdisc : NumberField.discr E ≠ 0` using `NumberField.discr_ne_zero E`. Take `⟨K, hK⟩ : ∃ K : ℤ, K = (M : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * (M : ℤ) ^ (Module.finrank ℤ Dw.La * n) * (2 * NumberField.discr E * M) ^ d` from `⟨_, rfl⟩`. Establish `hK0 : K.natAbs ≠ 0`.

Rewrite using `[Int.natAbs_ne_zero, hK]`. Establish `hM' : (M : ℤ) ≠ 0` using `by exact_mod_cast hM`. Conclude with `mul_ne_zero (mul_ne_zero (pow_ne_zero _ hM') (pow_ne_zero _ hM')) (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hdisc) hM'))`. Take `⟨c, k, hk, hKk⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hK0 p hp1`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Introduce `l₂ pd u Λ hl hpd hu hΛ`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl`. Conclude with `hp1 (Nat.coprime_zero_left p |>.mp hu)`. Establish `hN : 0 < l₂.M * u` using `Nat.mul_pos (by have := l₂.three_le; omega) (Nat.pos_of_ne_zero hu0)`.

Establish `h1 : Λ.mIdx (l₂.M * u) (Dw.p + Dw.q) ∣ (l₂.M * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q))` using `mIdx_dvd Λ _ _ hN hΛ.2.2`. Establish `h2 : Nat.card (Fin n → LevQ Dw l₂) ∣ l₂.M ^ (Module.finrank ℤ Dw.La * n)`. Rewrite using `[Nat.card_fun, Nat.card_fin, pow_mul]`. Conclude with `pow_dvd_pow_of_dvd (card_levQ_dvd Dw l₂) n`. Establish `hcop : ∀ m : ℕ, ¬ p ∣ m → Nat.Coprime m p` using `fun m hm => Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)`.

Establish `hpd'` using `hcop pd hpd`. Use `⟨k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) * (pd * u) ^ d), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Nat.Coprime.mul_left (hcop k hk) (Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)) (Nat.Coprime.pow_left _ hpd')) (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)))`. Establish `hKd : K ∣ (K.natAbs : ℤ)` using `Int.dvd_natAbs.mpr dvd_rfl`. Establish `h12` using `Int.natCast_dvd_natCast.mpr (Nat.mul_dvd_mul h1 h2)`.

Establish `hprod : ((l₂.M * u : ℕ) : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * ((l₂.M : ℕ) : ℤ) ^ (Module.finrank ℤ Dw.La * n) * (2 * NumberField.discr E * ((l₂.M * u : ℕ) : ℤ)) ^ d = K * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) * (pd * …`. Rewrite using `[hK, hl]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hfin : ((p ^ c * (k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) * (pd * u) ^ d)) : ℕ) : ℤ) = (K.natAbs : ℤ) * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) * (pd * u) ^ d : ℕ) : ℤ)`.

Rewrite using `[hKk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfin]`. Use `dvd_trans ?_ (mul_dvd_mul_right hKd _)` and prove the remaining obligations.

Rewrite using `[← hprod]`. Move the coercions through the operations in `at h12 ⊢`. Conclude with `mul_dvd_mul h12 dvd_rfl`.
-/
theorem const_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (n d M p : ℕ), p.Prime → M ≠ 0 → ∃ c : ℕ, ∀ (l₂ : Geo.Tor.Level H) (pd u : ℕ) (Λ : GenLat E n), l₂.M = M * pd → ¬ p ∣ pd → Nat.Coprime u p → Λ.LevOK (l₂.M * u) l₂.M → ∃ u' : ℕ, Nat.Coprime u' p ∧ ((Λ.mIdx (l₂.M * u) (Dw.p + Dw.q) * Nat.card (Fin n → LevQ Dw l₂) : ℕ) : ℤ) * (2 * NumberField.discr E * (l₂.M * u : ℕ)) ^ d ∣ ((p ^ c * u' : ℕ) : ℤ) := by
  intro E _ _ _ H Dw n d M p hp hM
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  have hdisc : NumberField.discr E ≠ 0 := NumberField.discr_ne_zero E
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = (M : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) *
      (M : ℤ) ^ (Module.finrank ℤ Dw.La * n) * (2 * NumberField.discr E * M) ^ d := ⟨_, rfl⟩
  have hK0 : K.natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero, hK]
    have hM' : (M : ℤ) ≠ 0 := by exact_mod_cast hM
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hM') (pow_ne_zero _ hM'))
      (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero hdisc) hM'))
  obtain ⟨c, k, hk, hKk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0 p hp1
  refine ⟨c, ?_⟩
  intro l₂ pd u Λ hl hpd hu hΛ
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hp1 (Nat.coprime_zero_left p |>.mp hu)
  have hN : 0 < l₂.M * u := Nat.mul_pos (by have := l₂.three_le; omega) (Nat.pos_of_ne_zero hu0)
  have h1 : Λ.mIdx (l₂.M * u) (Dw.p + Dw.q) ∣ (l₂.M * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) :=
    mIdx_dvd Λ _ _ hN hΛ.2.2
  have h2 : Nat.card (Fin n → LevQ Dw l₂) ∣ l₂.M ^ (Module.finrank ℤ Dw.La * n) := by
    rw [Nat.card_fun, Nat.card_fin, pow_mul]
    exact pow_dvd_pow_of_dvd (card_levQ_dvd Dw l₂) n
  have hcop : ∀ m : ℕ, ¬ p ∣ m → Nat.Coprime m p := fun m hm =>
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have hpd' := hcop pd hpd
  refine ⟨k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
    (pd * u) ^ d), ?_, ?_⟩
  · exact Nat.Coprime.mul_left (hcop k hk) (Nat.Coprime.mul_left (Nat.Coprime.mul_left
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)) (Nat.Coprime.pow_left _ hpd'))
      (Nat.Coprime.pow_left _ (Nat.Coprime.mul_left hpd' hu)))
  · have hKd : K ∣ (K.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
    have h12 := Int.natCast_dvd_natCast.mpr (Nat.mul_dvd_mul h1 h2)
    have hprod : ((l₂.M * u : ℕ) : ℤ) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * ((l₂.M : ℕ) : ℤ) ^ (Module.finrank ℤ Dw.La * n) *
        (2 * NumberField.discr E * ((l₂.M * u : ℕ) : ℤ)) ^ d =
        K * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
          (pd * u) ^ d : ℕ) : ℤ) := by
      rw [hK, hl]
      push_cast
      ring
    have hfin : ((p ^ c * (k * ((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) * pd ^ (Module.finrank ℤ Dw.La * n) *
        (pd * u) ^ d)) : ℕ) : ℤ) = (K.natAbs : ℤ) * (((pd * u) ^ (Module.finrank ℚ E * n * (Dw.p + Dw.q)) *
          pd ^ (Module.finrank ℤ Dw.La * n) * (pd * u) ^ d : ℕ) : ℤ) := by
      rw [hKk]
      push_cast
      ring
    rw [hfin]
    refine dvd_trans ?_ (mul_dvd_mul_right hKd _)
    rw [← hprod]
    push_cast at h12 ⊢
    exact mul_dvd_mul h12 dvd_rfl

end GlobalTheory.ConstBound
