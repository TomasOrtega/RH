import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.PadicSubsetSums.StableGradedCounts.TWCutOperator
import Formalism.PadicSubsetSums.StableGradedCounts.TWCentralIdempotentIntegral
import Formalism.PadicSubsetSums.StableGradedCounts.TWExportTransfer
import Formalism.PadicSubsetSums.StableGradedCounts.TWLengthBaseChange
import Formalism.SharpRestriction.LevelLetterCocycles.GaloisEquivariantKeyFunction

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.IntegralHeckeForms

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section Comm

variable {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W] [Module R W]

/- English proof (translation)
Unfold `Formalism.MainNotions.IntegralHeckeForms.sIdx Formalism.MainNotions.IntegralHeckeForms.lenR Formalism.IrreducibleCountingLemmas.TW.sIdx Formalism.IrreducibleCountingLemmas.TW.relLen`. Use `push_cast`. Rewrite using `[sub_div]`.
-/
theorem sIdx_eq (l : ℕ) (M N : Submodule R W) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M N =
      (Formalism.IrreducibleCountingLemmas.TW.sIdx M N : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  unfold Formalism.MainNotions.IntegralHeckeForms.sIdx Formalism.MainNotions.IntegralHeckeForms.lenR Formalism.IrreducibleCountingLemmas.TW.sIdx Formalism.IrreducibleCountingLemmas.TW.relLen
  push_cast
  rw [sub_div]

/- English proof (translation)
Take `⟨n, f, hf⟩` from `Module.Finite.exists_fin' R X`. Set `li : Fin n → (R ⧸ Ideal.span {c}) →ₗ[R] X` to `fun i => Submodule.liftQ (Ideal.span {c}) (LinearMap.toSpanSingleton R X (f (Pi.single i 1))) (by`. Rewrite using `[Ideal.span, Submodule.span_le]`. Introduce and unpack `_ rfl`. Simplify using `[h])`.

Set `g : (Fin n → R ⧸ Ideal.span {c}) →ₗ[R] X` to `∑ i, (li i) ∘ₗ LinearMap.proj i`. Establish `hg : Function.Surjective g`. Introduce `x`. Take `⟨v, rfl⟩` from `hf x`. Use `⟨fun i => Submodule.Quotient.mk (v i), ?_⟩` and prove the remaining obligations.

Establish `hv : v = ∑ i, v i • (Pi.single i (1 : R) : Fin n → R)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_rhs => rw [hv]`. Simplify using `only [g, li, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_smul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `erw [Submodule.liftQ_apply]`. Simplify using the standard rewrite rules. Use `ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective g hg)` and prove the remaining obligations. Rewrite using `[Module.length_pi]`.

Establish `h1 : Module.length R (R ⧸ Ideal.span {c}) ≠ ⊤` using `Formalism.IrreducibleCountingLemmas.TW.Idx.ord_ne_top' hc`. Take `⟨a, ha⟩` from `ENat.ne_top_iff_exists.1 h1`. Rewrite using `[← ha, ENat.card_eq_coe_fintype_card]`. Conclude with `ENat.natCast_ne_top _` after adjusting the coercions.
-/
theorem length_ne_top_of_smul_eq_zero {X : Type} [AddCommGroup X] [Module R X] [Module.Finite R X]
    (c : R) (hc : c ≠ 0) (h : ∀ x : X, c • x = 0) : Module.length R X ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R X
  let li : Fin n → (R ⧸ Ideal.span {c}) →ₗ[R] X := fun i =>
    Submodule.liftQ (Ideal.span {c}) (LinearMap.toSpanSingleton R X (f (Pi.single i 1))) (by
      rw [Ideal.span, Submodule.span_le]
      rintro _ rfl
      simp [h])
  let g : (Fin n → R ⧸ Ideal.span {c}) →ₗ[R] X := ∑ i, (li i) ∘ₗ LinearMap.proj i
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨v, rfl⟩ := hf x
    refine ⟨fun i => Submodule.Quotient.mk (v i), ?_⟩
    have hv : v = ∑ i, v i • (Pi.single i (1 : R) : Fin n → R) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hv]
    simp only [g, li, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    erw [Submodule.liftQ_apply]
    simp
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective g hg)
  rw [Module.length_pi]
  have h1 : Module.length R (R ⧸ Ideal.span {c}) ≠ ⊤ := Formalism.IrreducibleCountingLemmas.TW.Idx.ord_ne_top' hc
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 h1
  rw [← ha, ENat.card_eq_coe_fintype_card]
  exact_mod_cast ENat.natCast_ne_top _

/- English proof (translation)
Take `⟨S, hS⟩` from `hM.1`. Establish `hSV : ∀ s ∈ S, s ∈ V` using `fun s hs => hM.2.1 (hS ▸ Submodule.subset_span hs)`. Use `choose! c hc0 hcN using fun s (hs : s ∈ S) => hN.2.2 s (hSV s hs)`. Use `⟨∏ s ∈ S, c s, Finset.prod_ne_zero_iff.2 hc0, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[← hS]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem s hs`. Rewrite using `[← Finset.mul_prod_erase S c hs, mul_comm, mul_smul]`. Conclude with `N.smul_mem _ (hcN s hs)`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `N.add_mem hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `N.smul_mem _ hx`.
-/
theorem exists_smul_le {M N V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V) :
    ∃ c : R, c ≠ 0 ∧ ∀ x ∈ M, c • x ∈ N := by
  classical
  obtain ⟨S, hS⟩ := hM.1
  have hSV : ∀ s ∈ S, s ∈ V := fun s hs => hM.2.1 (hS ▸ Submodule.subset_span hs)
  choose! c hc0 hcN using fun s (hs : s ∈ S) => hN.2.2 s (hSV s hs)
  refine ⟨∏ s ∈ S, c s, Finset.prod_ne_zero_iff.2 hc0, ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem s hs =>
    rw [← Finset.mul_prod_erase S c hs, mul_comm, mul_smul]
    exact N.smul_mem _ (hcN s hs)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem _ hx

/- English proof (translation)
Take `⟨c, hc, h⟩` from `exists_smul_le hM hN`. Establish `: Module.Finite R M` using `Module.Finite.iff_fg.2 hM.1`. Unfold `relLen`. Use `length_ne_top_of_smul_eq_zero c hc ?_` and prove the remaining obligations. Introduce `x`.

Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `h m m.2`.
-/
theorem relLen_ne_top {M N V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V) :
    relLen M N ≠ ⊤ := by
  obtain ⟨c, hc, h⟩ := exists_smul_le hM hN
  have : Module.Finite R M := Module.Finite.iff_fg.2 hM.1
  unfold relLen
  refine length_ne_top_of_smul_eq_zero c hc ?_
  intro x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact h m m.2

/- English proof (translation)
Use `⟨?_, inf_le_left.trans hM.2.1, ?_⟩` and prove the remaining obligations. Establish `: IsNoetherian R M` using `isNoetherian_of_fg_of_noetherian M hM.1`. Establish `h2 : ((M ⊓ N).comap M.subtype).FG` using `IsNoetherian.noetherian _`. Establish `h3` using `h2.map M.subtype`. Rewrite `h3` using `[Submodule.map_comap_subtype, inf_eq_right.2 inf_le_left]`. Then use the resulting hypothesis.

Introduce `x hx`. Take `⟨c, hc, h⟩` from `hM.2.2 x hx`. Take `⟨c', hc', h'⟩` from `hN.2.2 x hx`. Use `⟨c * c', mul_ne_zero hc hc', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `M.smul_mem _ h`. Rewrite using `[mul_smul]`. Conclude with `N.smul_mem _ h'`.
-/
theorem isLatIn_inf {M N V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V) :
    IsLatIn (M ⊓ N) V := by
  refine ⟨?_, inf_le_left.trans hM.2.1, ?_⟩
  · have : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M hM.1
    have h2 : ((M ⊓ N).comap M.subtype).FG := IsNoetherian.noetherian _
    have h3 := h2.map M.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 inf_le_left] at h3
  · intro x hx
    obtain ⟨c, hc, h⟩ := hM.2.2 x hx
    obtain ⟨c', hc', h'⟩ := hN.2.2 x hx
    refine ⟨c * c', mul_ne_zero hc hc', ?_, ?_⟩
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h
    · rw [mul_smul]; exact N.smul_mem _ h'

/- English proof (translation)
Establish `h1` using `Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_tower (le_inf hQM hQN) (inf_le_left : M ⊓ N ≤ M)`. Establish `h2` using `Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_tower (le_inf hQM hQN) (inf_le_right : M ⊓ N ≤ N)`. Rewrite `h1` using `[Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf]`. Rewrite `h2` using `[inf_comm, Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf]`. Establish `f0` using `relLen_ne_top (isLatIn_inf hN hM) hQ`.

Establish `f1` using `relLen_ne_top hM hN`. Establish `f2` using `relLen_ne_top hN hM`. Rewrite `h1` using `[inf_comm]`. Unfold `Formalism.IrreducibleCountingLemmas.TW.sIdx`. Rewrite using `[h1, h2, ENat.toNat_add f0 f1, ENat.toNat_add f0 f2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sIdx_eq_sub {M N Q V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V)
    (hQ : IsLatIn Q V) (hQM : Q ≤ M) (hQN : Q ≤ N) :
    Formalism.IrreducibleCountingLemmas.TW.sIdx M N = ((relLen M Q).toNat : ℤ) - ((relLen N Q).toNat : ℤ) := by
  have h1 := Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_tower (le_inf hQM hQN) (inf_le_left : M ⊓ N ≤ M)
  have h2 := Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_tower (le_inf hQM hQN) (inf_le_right : M ⊓ N ≤ N)
  rw [Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf] at h1
  rw [inf_comm, Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf] at h2
  have f0 := relLen_ne_top (isLatIn_inf hN hM) hQ
  have f1 := relLen_ne_top hM hN
  have f2 := relLen_ne_top hN hM
  rw [inf_comm] at h1
  unfold Formalism.IrreducibleCountingLemmas.TW.sIdx
  rw [h1, h2, ENat.toNat_add f0 f1, ENat.toNat_add f0 f2]
  push_cast
  ring

/- English proof (translation)
Establish `hQ` using `isLatIn_inf (isLatIn_inf hM hN) hP`. Establish `q1 : M ⊓ N ⊓ P ≤ M` using `inf_le_left.trans inf_le_left`. Establish `q2 : M ⊓ N ⊓ P ≤ N` using `inf_le_left.trans inf_le_right`. Establish `q3 : M ⊓ N ⊓ P ≤ P` using `inf_le_right`. Rewrite using `[sIdx_eq_sub hM hN hQ q1 q2, sIdx_eq_sub hN hP hQ q2 q3, sIdx_eq_sub hM hP hQ q1 q3]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sIdx_add {M N P V : Submodule R W} (hM : IsLatIn M V) (hN : IsLatIn N V) (hP : IsLatIn P V) :
    Formalism.IrreducibleCountingLemmas.TW.sIdx M N + Formalism.IrreducibleCountingLemmas.TW.sIdx N P = Formalism.IrreducibleCountingLemmas.TW.sIdx M P := by
  have hQ := isLatIn_inf (isLatIn_inf hM hN) hP
  have q1 : M ⊓ N ⊓ P ≤ M := inf_le_left.trans inf_le_left
  have q2 : M ⊓ N ⊓ P ≤ N := inf_le_left.trans inf_le_right
  have q3 : M ⊓ N ⊓ P ≤ P := inf_le_right
  rw [sIdx_eq_sub hM hN hQ q1 q2, sIdx_eq_sub hN hP hQ q2 q3, sIdx_eq_sub hM hP hQ q1 q3]
  ring

/- English proof (translation)
Establish `a` using `sIdx_add hM hN hN'`. Establish `b` using `sIdx_add hM' hN hN'`. Establish `c : Formalism.IrreducibleCountingLemmas.TW.sIdx M N' - Formalism.IrreducibleCountingLemmas.TW.sIdx M N = Formalism.IrreducibleCountingLemmas.TW.sIdx M' N' - Formalism.IrreducibleCountingLemmas.TW.sIdx M' N` using `by omega`. Simplify using `only [sIdx_eq, ← sub_div]`. Use `congr 1`.

Conclude with `c` after adjusting the coercions.
-/
theorem sIdx_diff (l : ℕ) {M M' N N' V : Submodule R W} (hM : IsLatIn M V) (hM' : IsLatIn M' V)
    (hN : IsLatIn N V) (hN' : IsLatIn N' V) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M N' - Formalism.MainNotions.IntegralHeckeForms.sIdx l M N =
      Formalism.MainNotions.IntegralHeckeForms.sIdx l M' N' - Formalism.MainNotions.IntegralHeckeForms.sIdx l M' N := by
  have a := sIdx_add hM hN hN'
  have b := sIdx_add hM' hN hN'
  have c : Formalism.IrreducibleCountingLemmas.TW.sIdx M N' - Formalism.IrreducibleCountingLemmas.TW.sIdx M N =
      Formalism.IrreducibleCountingLemmas.TW.sIdx M' N' - Formalism.IrreducibleCountingLemmas.TW.sIdx M' N := by omega
  simp only [sIdx_eq, ← sub_div]
  congr 1
  exact_mod_cast c

end Comm

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section BaseChange

variable {R R' W W' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
  [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W'] [Module R' W'] [IsScalarTower R R' W']

def ext (R' : Type) {R W W' : Type} [CommRing R] [CommRing R'] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] [Module R' W'] (ι : W →ₗ[R] W') (N : Submodule R W) :
    Submodule R' W' :=
  Submodule.span R' (ι '' N)

/- English proof (translation)
Rewrite using `[← Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf]`. Unfold `relLen`. Conclude with `(LinearMap.quotientInfEquivSupQuotient M N).length_eq`.
-/
theorem relLen_sup {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (M N : Submodule R W) :
    relLen M N = relLen (M ⊔ N) N := by
  rw [← Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_inf]
  unfold relLen
  exact (LinearMap.quotientInfEquivSupQuotient M N).length_eq

variable {ι : W →ₗ[R] W'}

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `ext`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨m, hm, n, hn, rfl⟩` from `Submodule.mem_sup.1 hx`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨m, hm, rfl⟩)) (Submodule.mem_sup_right (Submodule.subset_span ⟨n, hn, rfl⟩))`. Conclude with `sup_le (Submodule.span_mono (Set.image_mono (le_sup_left (a := M) (b := N)))) (Submodule.span_mono (Set.image_mono (le_sup_right (a := M) (b := N))))`.
-/
theorem ext_sup (M N : Submodule R W) : ext R' ι (M ⊔ N) = ext R' ι M ⊔ ext R' ι N := by
  apply le_antisymm
  · unfold ext
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨m, hm, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨n, hn, rfl⟩))
  · exact sup_le (Submodule.span_mono (Set.image_mono (le_sup_left (a := M) (b := N))))
      (Submodule.span_mono (Set.image_mono (le_sup_right (a := M) (b := N))))

variable (hι : IsBaseChange R' ι)

def th (P : Submodule R W) : R' ⊗[R] P →ₗ[R'] W' :=
  hι.equiv.toLinearMap ∘ₗ P.subtype.baseChange R'

/- English proof (translation)
Simplify using `[th, IsBaseChange.equiv_tmul]`.
-/
theorem th_tmul (P : Submodule R W) (a : R') (p : P) : th hι P (a ⊗ₜ p) = a • ι p := by
  simp [th, IsBaseChange.equiv_tmul]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨t, rfl⟩`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a p`.

Rewrite using `[th_tmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, p.2, rfl⟩)`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Unfold `ext`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Conclude with `⟨1 ⊗ₜ ⟨p, hp⟩, by rw [th_tmul, one_smul]⟩`.
-/
theorem range_th (P : Submodule R W) : LinearMap.range (th hι P) = ext R' ι P := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      rw [th_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, p.2, rfl⟩)
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  · unfold ext
    rw [Submodule.span_le]
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨1 ⊗ₜ ⟨p, hp⟩, by rw [th_tmul, one_smul]⟩

/- English proof (translation)
Use `hι.equiv.injective.comp ?_` and prove the remaining obligations. Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap (M := R') P.subtype P.injective_subtype`.
-/
theorem th_injective [Module.Flat R R'] (P : Submodule R W) : Function.Injective (th hι P) := by
  refine hι.equiv.injective.comp ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := R') P.subtype P.injective_subtype

include hι in
/- English proof (translation)
Use `set N₀ := N.comap P.subtype with hN₀`. Set `φ : R' ⊗[R] P →ₗ[R'] (ext R' ι P ⧸ (ext R' ι N).comap (ext R' ι P).subtype)` to `(Submodule.mkQ _) ∘ₗ (LinearMap.codRestrict (ext R' ι P) (th hι P) (fun t => range_th hι P ▸ ⟨t, rfl⟩))`. Set `ψ : R' ⊗[R] P →ₗ[R'] R' ⊗[R] (P ⧸ N₀)` to `N₀.mkQ.baseChange R'`. Establish `hφ : Function.Surjective φ`. Introduce `x`.

Take `⟨⟨y, hy⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hy` using `[← range_th hι P]`. Take `⟨t, rfl⟩` from `hy`. Conclude with `⟨t, rfl⟩`. Establish `hψ : Function.Surjective ψ` using `by show Function.Surjective (N₀.mkQ.baseChange R')`.

Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)`. Establish `kψ : ∀ t, ψ t = 0 ↔ t ∈ LinearMap.range (N₀.subtype.baseChange R')`. Introduce `t`. Use `lTensor_exact R' (LinearMap.exact_subtype_mkQ N₀) (Submodule.mkQ_surjective N₀) t` as an intermediate fact.

Conclude with `this`. Establish `kφ : ∀ t, φ t = 0 ↔ t ∈ LinearMap.range (N₀.subtype.baseChange R')`. Introduce `t`. Establish `h0 : φ t = 0 ↔ th hι P t ∈ ext R' ι N` using `by show Submodule.Quotient.mk _ = 0 ↔ _`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Both sides reduce to the same expression. Rewrite using `[h0]`. Prove the components needed by the constructor for the conclusion. Introduce `ht`. Establish `hle : ext R' ι N ≤ (LinearMap.range (N₀.subtype.baseChange R')).map (th hι P)`.

Unfold `ext`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Use `⟨1 ⊗ₜ ⟨n, h hn⟩, ⟨1 ⊗ₜ ⟨⟨n, h hn⟩, hn⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Rewrite using `[th_tmul, one_smul]`. Take `⟨s, hs, hst⟩` from `hle ht`. Rewrite using `[← th_injective hι P hst]` and apply the resulting hypothesis. Introduce and unpack `⟨s, rfl⟩ clear h0`. Proceed by induction on `s using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a n`. Rewrite using `[LinearMap.baseChange_tmul, th_tmul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, n.2, rfl⟩)`. Consider the case `add x y hx hy => rw [map_add, map_add]`.

Conclude with `Submodule.add_mem _ hx hy`. Establish `hk : LinearMap.ker φ = LinearMap.ker ψ`. Use extensionality with `t`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_ker, kφ, kψ]`. Unfold `relLen`.

Conclude with `((φ.quotKerEquivOfSurjective hφ).symm.trans ((Submodule.quotEquivOfEq _ _ hk).trans (ψ.quotKerEquivOfSurjective hψ))).length_eq`.
-/
theorem relLen_ext_of_le [Module.Flat R R'] {N P : Submodule R W} (h : N ≤ P) :
    relLen (ext R' ι P) (ext R' ι N) = Module.length R' (R' ⊗[R] (P ⧸ N.comap P.subtype)) := by
  set N₀ := N.comap P.subtype with hN₀
  let φ : R' ⊗[R] P →ₗ[R'] (ext R' ι P ⧸ (ext R' ι N).comap (ext R' ι P).subtype) :=
    (Submodule.mkQ _) ∘ₗ (LinearMap.codRestrict (ext R' ι P) (th hι P)
      (fun t => range_th hι P ▸ ⟨t, rfl⟩))
  let ψ : R' ⊗[R] P →ₗ[R'] R' ⊗[R] (P ⧸ N₀) := N₀.mkQ.baseChange R'
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [← range_th hι P] at hy
    obtain ⟨t, rfl⟩ := hy
    exact ⟨t, rfl⟩
  have hψ : Function.Surjective ψ := by
    show Function.Surjective (N₀.mkQ.baseChange R')
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
  have kψ : ∀ t, ψ t = 0 ↔ t ∈ LinearMap.range (N₀.subtype.baseChange R') := by
    intro t
    have := lTensor_exact R' (LinearMap.exact_subtype_mkQ N₀) (Submodule.mkQ_surjective N₀) t
    exact this
  have kφ : ∀ t, φ t = 0 ↔ t ∈ LinearMap.range (N₀.subtype.baseChange R') := by
    intro t
    have h0 : φ t = 0 ↔ th hι P t ∈ ext R' ι N := by
      show Submodule.Quotient.mk _ = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      rfl
    rw [h0]
    constructor
    · intro ht
      have hle : ext R' ι N ≤ (LinearMap.range (N₀.subtype.baseChange R')).map (th hι P) := by
        unfold ext
        rw [Submodule.span_le]
        rintro _ ⟨n, hn, rfl⟩
        refine ⟨1 ⊗ₜ ⟨n, h hn⟩, ⟨1 ⊗ₜ ⟨⟨n, h hn⟩, hn⟩, ?_⟩, ?_⟩
        · simp
        · rw [th_tmul, one_smul]
      obtain ⟨s, hs, hst⟩ := hle ht
      rwa [← th_injective hι P hst]
    · rintro ⟨s, rfl⟩
      clear h0
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a n =>
        rw [LinearMap.baseChange_tmul, th_tmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, n.2, rfl⟩)
      | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  have hk : LinearMap.ker φ = LinearMap.ker ψ := by
    ext t
    rw [LinearMap.mem_ker, LinearMap.mem_ker, kφ, kψ]
  unfold relLen
  exact ((φ.quotKerEquivOfSurjective hφ).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk).trans (ψ.quotKerEquivOfSurjective hψ))).length_eq

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Take `⟨ϖ', hϖ'⟩` from `IsDiscreteValuationRing.exists_irreducible R'`. Establish `hne : algebraMap R R' ϖ ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ hinj]`. Conclude with `hϖ.ne_zero`.

Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ'`. Use `⟨ϖ, ϖ', u, e, hϖ, hϖ', hu, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos e with rfl | he` into its components or cases. It suffices to derive a contradiction. Establish `: FaithfulSMul R R'` using `(faithfulSMul_iff_algebraMap_injective R R').mpr hinj`.

Establish `hl : IsLocalHom (algebraMap R R')` using `inferInstance`. Use `hϖ.not_isUnit (hl.map_nonunit ϖ ?_)` and prove the remaining obligations. Rewrite using `[hu, pow_zero, mul_one]`. Conclude with `u.isUnit`. Conclude with `he`.
-/
theorem exists_ram (hinj : Function.Injective (algebraMap R R')) [Algebra.IsIntegral R R'] :
    ∃ (ϖ : R) (ϖ' : R') (u : R'ˣ) (e : ℕ), Irreducible ϖ ∧ Irreducible ϖ' ∧
      algebraMap R R' ϖ = (u : R') * ϖ' ^ e ∧ 0 < e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible R'
  have hne : algebraMap R R' ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hϖ.ne_zero
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ'
  refine ⟨ϖ, ϖ', u, e, hϖ, hϖ', hu, ?_⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exfalso
    have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj
    have hl : IsLocalHom (algebraMap R R') := inferInstance
    refine hϖ.not_isUnit (hl.map_nonunit ϖ ?_)
    rw [hu, pow_zero, mul_one]
    exact u.isUnit
  · exact he

variable {ϖ : R} {ϖ' : R'} {u : R'ˣ} {e : ℕ}

/- English proof (translation)
Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using the standard rewrite rules. Take `⟨n, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ`. Rewrite using `[IsDiscreteValuationRing.addVal_def _ v hϖ n rfl, IsDiscreteValuationRing.addVal_def _ (Units.map (algebraMap R R').toMonoidHom v * u ^ n) hϖ' (e * n) (by rw [map_mul, map_pow, hu]; push_cast; simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]; ring)]`. Simplify using the standard rewrite rules.
-/
theorem addVal_map (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (hu : algebraMap R R' ϖ = (u : R') * ϖ' ^ e) (x : R) :
    (IsDiscreteValuationRing.addVal R' (algebraMap R R' x)).toNat =
      e * (IsDiscreteValuationRing.addVal R x).toNat := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [IsDiscreteValuationRing.addVal_def _ v hϖ n rfl,
      IsDiscreteValuationRing.addVal_def _ (Units.map (algebraMap R R').toMonoidHom v * u ^ n) hϖ' (e * n)
        (by rw [map_mul, map_pow, hu]; push_cast; simp only [Units.coe_map, MonoidHom.coe_coe,
              RingHom.toMonoidHom_eq_coe]; ring)]
    simp

include hι in
/- English proof (translation)
Rewrite using `[relLen_sup, ← ext_sup, relLen_ext_of_le hι le_sup_right, relLen_sup M N]`. Rewrite `hfin` using `[relLen_sup]`. Conclude with `Formalism.IrreducibleCountingLemmas.TW.length_base_change_dvr R R' ϖ ϖ' u e hϖ hϖ' hu he _ hfin`.
-/
theorem relLen_ext (hϖ : Irreducible ϖ) (hϖ' : Irreducible ϖ')
    (hu : algebraMap R R' ϖ = (u : R') * ϖ' ^ e) (he : 0 < e) [Module.Flat R R']
    {M N : Submodule R W} (hfin : relLen M N ≠ ⊤) :
    relLen (ext R' ι M) (ext R' ι N) = (e : ℕ∞) * relLen M N := by
  rw [relLen_sup, ← ext_sup, relLen_ext_of_le hι le_sup_right, relLen_sup M N]
  rw [relLen_sup] at hfin
  exact Formalism.IrreducibleCountingLemmas.TW.length_base_change_dvr R R' ϖ ϖ' u e hϖ hϖ' hu he _ hfin

include hι in

/- English proof (translation)
Take `⟨ϖ, ϖ', u, e, hϖ, hϖ', hu, he⟩` from `exists_ram (R := R) (R' := R') hinj`. Establish `: FaithfulSMul R R'` using `(faithfulSMul_iff_algebraMap_injective R R').mpr hinj`. Establish `: Module.IsTorsionFree R R'` using `inferInstance`. Establish `: Module.Flat R R'` using `inferInstance`. Rewrite using `[sIdx_eq, sIdx_eq]`.

Unfold `Formalism.IrreducibleCountingLemmas.TW.sIdx`. Rewrite using `[relLen_ext hι hϖ hϖ' hu he h1, relLen_ext hι hϖ hϖ' hu he h2, ← map_natCast (algebraMap R R') l, addVal_map hϖ hϖ' hu, ENat.toNat_mul, ENat.toNat_mul, ENat.toNat_natCast]`. Use `push_cast`. Rewrite using `[← mul_sub, mul_div_mul_left _ _ (by exact_mod_cast he.ne')]`.
-/
theorem sIdx_ext (hinj : Function.Injective (algebraMap R R')) [Algebra.IsIntegral R R'] (l : ℕ)
    {M N : Submodule R W} (h1 : relLen M N ≠ ⊤) (h2 : relLen N M ≠ ⊤) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l (ext R' ι M) (ext R' ι N) = Formalism.MainNotions.IntegralHeckeForms.sIdx l M N := by
  obtain ⟨ϖ, ϖ', u, e, hϖ, hϖ', hu, he⟩ := exists_ram (R := R) (R' := R') hinj
  have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').mpr hinj
  have : Module.IsTorsionFree R R' := inferInstance
  have : Module.Flat R R' := inferInstance
  rw [sIdx_eq, sIdx_eq]
  unfold Formalism.IrreducibleCountingLemmas.TW.sIdx
  rw [relLen_ext hι hϖ hϖ' hu he h1, relLen_ext hι hϖ hϖ' hu he h2, ← map_natCast (algebraMap R R') l,
    addVal_map hϖ hϖ' hu, ENat.toNat_mul, ENat.toNat_mul, ENat.toNat_natCast]
  push_cast
  rw [← mul_sub, mul_div_mul_left _ _ (by exact_mod_cast he.ne')]

end BaseChange

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section Transfer

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `ext`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[map_smul, ← algebraMap_smul R' a (ι x)]`. Conclude with `Submodule.smul_mem _ _ hx`. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem ext_span {R R' W W' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] [Module R' W'] [IsScalarTower R R' W'] (ι : W →ₗ[R] W') (s : Set W) :
    ext R' ι (Submodule.span R s) = Submodule.span R' (ι '' s) := by
  apply le_antisymm
  · unfold ext
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul, ← algebraMap_smul R' a (ι x)]
      exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Rewrite using `[Submodule.baseChange_eq_span]`. Both sides reduce to the same expression.
-/
theorem baseChange_eq_ext {R W : Type} (A : Type) [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup W]
    [Module R W] (N : Submodule R W) : N.baseChange A = ext A (TensorProduct.mk R A W 1) N := by
  rw [Submodule.baseChange_eq_span]
  rfl

/- English proof (translation)
Use `⟨?_, Submodule.span_mono (Set.image_mono h.2.1), ?_⟩` and prove the remaining obligations. Take `⟨S, hS⟩` from `h.1`. Rewrite using `[← hS, ext_span]`. Conclude with `Submodule.fg_span (S.finite_toSet.image _)`. Introduce `x hx`.

Unfold `ext at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`. Take `⟨c, hc, hcv⟩` from `h.2.2 v hv`.

Use `⟨algebraMap R R' c, by rwa [Ne, map_eq_zero_iff _ hinj], ?_⟩` and prove the remaining obligations. Rewrite using `[algebraMap_smul, ← map_smul]`. Conclude with `Submodule.subset_span ⟨_, hcv, rfl⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨c, hc, h1⟩` from `hx`. Take `⟨c', hc', h2⟩` from `hy`. Use `⟨c * c', mul_ne_zero hc hc', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `Submodule.smul_mem _ _ h1`. Rewrite using `[mul_smul]`. Conclude with `Submodule.smul_mem _ _ h2`. Consider the case `smul a x _ hx`.

Take `⟨c, hc, h1⟩` from `hx`. Conclude with `⟨c, hc, by rw [smul_comm]; exact Submodule.smul_mem _ _ h1⟩`.
-/
theorem isLatIn_ext {R R' W W' : Type} [CommRing R] [CommRing R'] [IsDomain R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] [Module R' W'] [IsScalarTower R R' W'] (ι : W →ₗ[R] W')
    {N V : Submodule R W} (h : IsLatIn N V) : IsLatIn (ext R' ι N) (ext R' ι V) := by
  refine ⟨?_, Submodule.span_mono (Set.image_mono h.2.1), ?_⟩
  · obtain ⟨S, hS⟩ := h.1
    rw [← hS, ext_span]
    exact Submodule.fg_span (S.finite_toSet.image _)
  · intro x hx
    unfold ext at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨c, hc, hcv⟩ := h.2.2 v hv
      refine ⟨algebraMap R R' c, by rwa [Ne, map_eq_zero_iff _ hinj], ?_⟩
      rw [algebraMap_smul, ← map_smul]
      exact Submodule.subset_span ⟨_, hcv, rfl⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, h1⟩ := hx
      obtain ⟨c', hc', h2⟩ := hy
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ h1
      · rw [mul_smul]; exact Submodule.smul_mem _ _ h2
    | smul a x _ hx =>
      obtain ⟨c, hc, h1⟩ := hx
      exact ⟨c, hc, by rw [smul_comm]; exact Submodule.smul_mem _ _ h1⟩

variable {O Ok O' Fm : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing Ok] [IsDomain Ok] [IsDiscreteValuationRing Ok] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O Ok] [Algebra Ok O'] [Algebra O O'] [IsScalarTower O Ok O']
  [AddCommGroup Fm] [Module O Fm]

variable (O Ok O' Fm) in

def gk : Ok ⊗[O] Fm →ₗ[Ok] O' ⊗[O] Fm :=
  TensorProduct.AlgebraTensorModule.map (Algebra.linearMap Ok O') LinearMap.id

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a f => simp [gk]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem gk_apply (t : Ok ⊗[O] Fm) :
    gk O Ok O' Fm t = LinearMap.rTensor Fm (IsScalarTower.toAlgHom O Ok O').toLinearMap t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a f => simp [gk]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Use extensionality with `f`. Simplify using `[gk]`.
-/
theorem gk_comp : (gk O Ok O' Fm).restrictScalars O ∘ₗ TensorProduct.mk O Ok Fm 1 =
    TensorProduct.mk O O' Fm 1 := by
  ext f
  simp [gk]

/- English proof (translation)
Use `IsBaseChange.of_comp (TensorProduct.isBaseChange O Fm Ok) ?_` and prove the remaining obligations. Use `TensorProduct.isBaseChange O Fm O'` as an intermediate fact. Rewrite `this` using `[← gk_comp (Ok := Ok)]`. Conclude with `this`.
-/
theorem gk_isBaseChange : IsBaseChange O' (gk O Ok O' Fm) := by
  refine IsBaseChange.of_comp (TensorProduct.isBaseChange O Fm Ok) ?_
  have := TensorProduct.isBaseChange O Fm O'
  rw [← gk_comp (Ok := Ok)] at this
  exact this

/- English proof (translation)
Rewrite using `[Submodule.baseChange_eq_span, ext_span, Submodule.baseChange_eq_span]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨n, hn, rfl⟩, rfl⟩`.

Conclude with `⟨n, hn, (LinearMap.congr_fun (gk_comp (O := O) (Ok := Ok) (O' := O') (Fm := Fm)) n).symm⟩`. Introduce and unpack `⟨n, hn, rfl⟩`. Conclude with `⟨_, ⟨n, hn, rfl⟩, LinearMap.congr_fun (gk_comp (O := O) (Ok := Ok) (O' := O') (Fm := Fm)) n⟩`.
-/
theorem ext_gk (N : Submodule O Fm) : ext O' (gk O Ok O' Fm) (N.baseChange Ok) = N.baseChange O' := by
  rw [Submodule.baseChange_eq_span, ext_span, Submodule.baseChange_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨n, hn, (LinearMap.congr_fun (gk_comp (O := O) (Ok := Ok) (O' := O') (Fm := Fm)) n).symm⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨_, ⟨n, hn, rfl⟩, LinearMap.congr_fun (gk_comp (O := O) (Ok := Ok) (O' := O') (Fm := Fm)) n⟩

/- English proof (translation)
Establish `h3 : Function.Injective (algebraMap O O')`. Rewrite using `[IsScalarTower.algebraMap_eq O Ok O']`. Conclude with `h2.comp h1`. Establish `: Module.Finite O O'` using `Module.Finite.trans Ok O'`. Establish `hT1 : Submodule.span O' ((LinearMap.rTensor Fm (IsScalarTower.toAlgHom O Ok O').toLinearMap) '' (Tψ : Set (Ok ⊗[O] Fm))) =`.

Use extensionality with `O' (gk O Ok O' Fm) Tψ := by`. Unfold `ext`. Rewrite using `[Set.image_congr fun t _ => (gk_apply (O' := O') t).symm]`. Rewrite using `[hT1]`. Establish `lB' : IsLatIn (B.baseChange O') (V.baseChange O')`.

Rewrite using `[baseChange_eq_ext, baseChange_eq_ext]`. Conclude with `isLatIn_ext h3 _ hB`. Establish `lT2 : IsLatIn (T.baseChange O') (V.baseChange O')`. Rewrite using `[baseChange_eq_ext, baseChange_eq_ext]`. Conclude with `isLatIn_ext h3 _ hT`.

Establish `lBk : IsLatIn (B.baseChange Ok) (V.baseChange Ok)`. Rewrite using `[baseChange_eq_ext, baseChange_eq_ext]`. Conclude with `isLatIn_ext h1 _ hB`. Establish `lT1 : IsLatIn (ext O' (gk O Ok O' Fm) Tψ) (V.baseChange O')`. Rewrite using `[← ext_gk (Ok := Ok) V]`.

Conclude with `isLatIn_ext h2 _ hTψ`. Establish `d` using `sIdx_diff l hM lB' lT2 lT1`. Establish `e1 : Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange O') (T.baseChange O') = Formalism.MainNotions.IntegralHeckeForms.sIdx l B T`. Rewrite using `[baseChange_eq_ext, baseChange_eq_ext]`. Conclude with `sIdx_ext (TensorProduct.isBaseChange O Fm O') h3 l (relLen_ne_top hB hT) (relLen_ne_top hT hB)`.

Establish `e2 : Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange O') (ext O' (gk O Ok O' Fm) Tψ) = Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange Ok) Tψ`. Rewrite using `[← ext_gk (Ok := Ok) B]`. Conclude with `sIdx_ext gk_isBaseChange h2 l (relLen_ne_top lBk hTψ) (relLen_ne_top hTψ lBk)`. Rewrite `d` using `[e1, e2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem transfer (h1 : Function.Injective (algebraMap O Ok)) [Module.Finite O Ok]
    (h2 : Function.Injective (algebraMap Ok O')) [Module.Finite Ok O'] (l : ℕ)
    {B T V : Submodule O Fm} {Tψ : Submodule Ok (Ok ⊗[O] Fm)} (hB : IsLatIn B V) (hT : IsLatIn T V)
    (hTψ : IsLatIn Tψ (V.baseChange Ok)) (e : ℝ)
    (h : Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange Ok) Tψ ≤ Formalism.MainNotions.IntegralHeckeForms.sIdx l B T + e)
    {M : Submodule O' (O' ⊗[O] Fm)} (hM : IsLatIn M (V.baseChange O')) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M (Submodule.span O'
              ((LinearMap.rTensor Fm (IsScalarTower.toAlgHom O Ok O').toLinearMap) '' (Tψ : Set (Ok ⊗[O] Fm)))) ≤
      Formalism.MainNotions.IntegralHeckeForms.sIdx l M (T.baseChange O') + e := by
  have h3 : Function.Injective (algebraMap O O') := by
    rw [IsScalarTower.algebraMap_eq O Ok O']
    exact h2.comp h1
  have : Module.Finite O O' := Module.Finite.trans Ok O'
  have hT1 : Submodule.span O'
      ((LinearMap.rTensor Fm (IsScalarTower.toAlgHom O Ok O').toLinearMap) '' (Tψ : Set (Ok ⊗[O] Fm))) =
      ext O' (gk O Ok O' Fm) Tψ := by
    unfold ext
    rw [Set.image_congr fun t _ => (gk_apply (O' := O') t).symm]
  rw [hT1]
  have lB' : IsLatIn (B.baseChange O') (V.baseChange O') := by
    rw [baseChange_eq_ext, baseChange_eq_ext]; exact isLatIn_ext h3 _ hB
  have lT2 : IsLatIn (T.baseChange O') (V.baseChange O') := by
    rw [baseChange_eq_ext, baseChange_eq_ext]; exact isLatIn_ext h3 _ hT
  have lBk : IsLatIn (B.baseChange Ok) (V.baseChange Ok) := by
    rw [baseChange_eq_ext, baseChange_eq_ext]; exact isLatIn_ext h1 _ hB
  have lT1 : IsLatIn (ext O' (gk O Ok O' Fm) Tψ) (V.baseChange O') := by
    rw [← ext_gk (Ok := Ok) V]; exact isLatIn_ext h2 _ hTψ
  have d := sIdx_diff l hM lB' lT2 lT1
  have e1 : Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange O') (T.baseChange O') = Formalism.MainNotions.IntegralHeckeForms.sIdx l B T := by
    rw [baseChange_eq_ext, baseChange_eq_ext]
    exact sIdx_ext (TensorProduct.isBaseChange O Fm O') h3 l (relLen_ne_top hB hT) (relLen_ne_top hT hB)
  have e2 : Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange O') (ext O' (gk O Ok O' Fm) Tψ) =
      Formalism.MainNotions.IntegralHeckeForms.sIdx l (B.baseChange Ok) Tψ := by
    rw [← ext_gk (Ok := Ok) B]
    exact sIdx_ext gk_isBaseChange h2 l (relLen_ne_top lBk hTψ) (relLen_ne_top hTψ lBk)
  rw [e1, e2] at d
  linarith

end Transfer

end Idx

namespace Idx

open Formalism.IrreducibleCountingLemmas.TW (relLen)
open Formalism.MainNotions.IntegralHeckeForms (IsLatIn lenR)
open scoped TensorProduct

section More

variable {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W] [Module R W]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hfg, hTV, fun x hx => let ⟨c, hc, h⟩ := hY.2.2 x hx; ⟨c, hc, hYT h⟩⟩`.
-/
theorem isLatIn_of_le {Y T V : Submodule R W} (hY : IsLatIn Y V) (hfg : T.FG) (hYT : Y ≤ T) (hTV : T ≤ V) :
    IsLatIn T V :=
  ⟨hfg, hTV, fun x hx => let ⟨c, hc, h⟩ := hY.2.2 x hx; ⟨c, hc, hYT h⟩⟩

/- English proof (translation)
Unfold `relLen`. Use `(Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective φ hφ M) ?_).length_eq.symm` and prove the remaining obligations. Use extensionality with `⟨y, hy⟩`. Simplify using `only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, Subtype.exists]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, hxN, h⟩`. Use `⟨x, hxN, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val h` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨x, hxN, rfl⟩`.

Take `⟨x', hx', h⟩` from `hy`. Establish `: x' = x` using `hφ h`. Substitute `this` using the available equality. Conclude with `⟨x', hx', hxN, rfl⟩`.
-/
theorem relLen_map_of_injective {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W]
    [AddCommGroup W'] [Module R W'] (φ : W →ₗ[R] W') (hφ : Function.Injective φ) (M N : Submodule R W) :
    relLen (M.map φ) (N.map φ) = relLen M N := by
  unfold relLen
  refine (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective φ hφ M) ?_).length_eq.symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, Subtype.exists]
  constructor
  · rintro ⟨x, hx, hxN, h⟩
    refine ⟨x, hxN, ?_⟩
    have := congrArg Subtype.val h
    simpa using this
  · rintro ⟨x, hxN, rfl⟩
    obtain ⟨x', hx', h⟩ := hy
    have : x' = x := hφ h
    subst this
    exact ⟨x', hx', hxN, rfl⟩

/- English proof (translation)
Use `⟨hN.1.map _, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `V.smul_mem _ (hN.2.1 hx)`. Introduce `x hx`. Take `⟨c', hc', h⟩` from `hN.2.2 x hx`.

Use `⟨c * c', mul_ne_zero hc hc', ⟨c' • x, h, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, mul_smul]`.
-/
theorem isLatIn_smul {N V : Submodule R W} (hN : IsLatIn N V) {c : R} (hc : c ≠ 0) :
    IsLatIn (N.map (c • (LinearMap.id : W →ₗ[R] W))) V := by
  refine ⟨hN.1.map _, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact V.smul_mem _ (hN.2.1 hx)
  · intro x hx
    obtain ⟨c', hc', h⟩ := hN.2.2 x hx
    refine ⟨c * c', mul_ne_zero hc hc', ⟨c' • x, h, ?_⟩⟩
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq, mul_smul]

/- English proof (translation)
Establish `a` using `sIdx_add hM (isLatIn_smul h₂ hc) (isLatIn_smul h₁ hc)`. Establish `b` using `sIdx_add hM h₂ h₁`. Establish `e : Formalism.IrreducibleCountingLemmas.TW.sIdx (N₂.map (c • (LinearMap.id : W →ₗ[R] W))) (N₁.map (c • (LinearMap.id : W →ₗ[R] W))) = Formalism.IrreducibleCountingLemmas.TW.sIdx N₂ N₁`. Unfold `Formalism.IrreducibleCountingLemmas.TW.sIdx`. Rewrite using `[relLen_map_of_injective _ hinj, relLen_map_of_injective _ hinj]`.

Establish `d : Formalism.IrreducibleCountingLemmas.TW.sIdx M (N₁.map (c • (LinearMap.id : W →ₗ[R] W))) - Formalism.IrreducibleCountingLemmas.TW.sIdx M (N₂.map (c • (LinearMap.id : W →ₗ[R] W))) = Formalism.IrreducibleCountingLemmas.TW.sIdx M N₁ - Formalism.IrreducibleCountingLemmas.TW.sIdx M …` using `by omega`. Simplify using `only [sIdx_eq, ← sub_div]`. Use `congr 1`. Conclude with `d` after adjusting the coercions.
-/
theorem sIdx_smul_diff (l : ℕ) {M N₁ N₂ V : Submodule R W} (hM : IsLatIn M V) (h₁ : IsLatIn N₁ V)
    (h₂ : IsLatIn N₂ V) {c : R} (hc : c ≠ 0)
    (hinj : Function.Injective (c • (LinearMap.id : W →ₗ[R] W))) :
    Formalism.MainNotions.IntegralHeckeForms.sIdx l M (N₁.map (c • (LinearMap.id : W →ₗ[R] W))) -
              Formalism.MainNotions.IntegralHeckeForms.sIdx l M (N₂.map (c • (LinearMap.id : W →ₗ[R] W))) =
      Formalism.MainNotions.IntegralHeckeForms.sIdx l M N₁ - Formalism.MainNotions.IntegralHeckeForms.sIdx l M N₂ := by
  have a := sIdx_add hM (isLatIn_smul h₂ hc) (isLatIn_smul h₁ hc)
  have b := sIdx_add hM h₂ h₁
  have e : Formalism.IrreducibleCountingLemmas.TW.sIdx (N₂.map (c • (LinearMap.id : W →ₗ[R] W)))
      (N₁.map (c • (LinearMap.id : W →ₗ[R] W))) = Formalism.IrreducibleCountingLemmas.TW.sIdx N₂ N₁ := by
    unfold Formalism.IrreducibleCountingLemmas.TW.sIdx
    rw [relLen_map_of_injective _ hinj, relLen_map_of_injective _ hinj]
  have d : Formalism.IrreducibleCountingLemmas.TW.sIdx M (N₁.map (c • (LinearMap.id : W →ₗ[R] W))) -
      Formalism.IrreducibleCountingLemmas.TW.sIdx M (N₂.map (c • (LinearMap.id : W →ₗ[R] W))) =
      Formalism.IrreducibleCountingLemmas.TW.sIdx M N₁ - Formalism.IrreducibleCountingLemmas.TW.sIdx M N₂ := by omega
  simp only [sIdx_eq, ← sub_div]
  congr 1
  exact_mod_cast d

/- English proof (translation)
Use `set m := IsLocalRing.maximalIdeal R with hm`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `hϖm : ϖ ∈ m` using `by rw [hm, hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ`. Establish `: IsNoetherian R B` using `isNoetherian_of_fg_of_noetherian B hB.1`. Establish `fgle : ∀ N : Submodule R W, N ≤ B → N.FG`.

Introduce `N hN`. Establish `h2 : (N.comap B.subtype).FG` using `IsNoetherian.noetherian _`. Establish `h3` using `h2.map B.subtype`. Rewrite `h3` using `[Submodule.map_comap_subtype, inf_eq_right.2 hN]`. Then use the resulting hypothesis. Set `Nn : ℕ → Submodule R W` to `fun n => (m ^ n) • B`.

Establish `hNB : ∀ n, Nn n ≤ B` using `fun n => Submodule.smul_le_right`. Establish `hNlat : ∀ n, IsLatIn (Nn n) V`. Introduce `n`. Use `⟨fgle _ (hNB n), (hNB n).trans hB.2.1, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Take `⟨c, hc, h⟩` from `hB.2.2 x hx`. Use `⟨ϖ ^ n * c, mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) hc, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `Submodule.smul_mem_smul (Ideal.pow_mem_pow hϖm n) h`. Set `T : ℕ → Submodule R W` to `fun n => Y ⊔ Nn n`.

Establish `hT : ∀ n, IsLatIn (T n) V` using `fun n => isLatIn_of_le (hNlat n) (hfg.sup (hNlat n).1) le_sup_right (sup_le hYV (hNlat n).2.1)`. Distinguish the cases in `hex : ∃ n, Nn n ≤ Y`. Take `⟨n, hn⟩` from `hex`. Conclude with `isLatIn_of_le (hNlat n) hfg hn hYV`. It suffices to derive a contradiction.

Rewrite `hex` using `[not_exists]`. Establish `hsucc : ∀ n, Nn (n + 1) = m • Nn n`. Introduce `n`. Use `show (m ^ (n + 1)) • B = m • ((m ^ n) • B)`. Rewrite using `[pow_succ', Submodule.mul_smul]`.

Establish `hle : ∀ n, T (n + 1) ≤ T n`. Introduce `n`. Use `sup_le_sup_left ?_ Y` and prove the remaining obligations. Rewrite using `[hsucc]`. Conclude with `Submodule.smul_le_right`.

Establish `hne : ∀ n, ¬ T n ≤ T (n + 1)`. Introduce `n h`. Apply `hex n` to reduce the goal to its premises. Establish `h1 : Nn n ≤ Y ⊔ m • Nn n`. Rewrite using `[← hsucc]`.

Conclude with `le_sup_right.trans h`. Conclude with `Submodule.le_of_le_smul_of_le_jacobson_bot (hNlat n).1 (by rw [hm, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) h1`. Establish `hstep : ∀ n, Formalism.IrreducibleCountingLemmas.TW.sIdx B (T n) + 1 ≤ Formalism.IrreducibleCountingLemmas.TW.sIdx B (T (n + 1))`. Introduce `n`. Establish `a` using `sIdx_add hB (hT n) (hT (n + 1))`.

Establish `h0 : relLen (T (n + 1)) (T n) = 0` using `Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_of_le (hle n)`. Establish `h1 : relLen (T n) (T (n + 1)) ≠ 0`. Unfold `relLen`. Rewrite using `[Ne, Module.length_eq_zero_iff]`. Introduce `h`.

Use `hne n fun x hx => ?_` and prove the remaining obligations. Establish `h9` using `h.elim (Submodule.Quotient.mk (p := (T (n + 1)).comap (T n).subtype) ⟨x, hx⟩) 0`. Rewrite `h9` using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `h9`. Establish `h2` using `relLen_ne_top (hT n) (hT (n + 1))`.

Establish `h3 : 1 ≤ (relLen (T n) (T (n + 1))).toNat`. Take `⟨a, ha⟩` from `ENat.ne_top_iff_exists.1 h2`. Rewrite `h1`, the goal using `[← ha]`. Simplify using `only [ENat.toNat_natCast]`. Establish `: a ≠ 0` using `by rintro rfl; exact h1 rfl`.

Use linear arithmetic over natural numbers and integers. Establish `h4 : Formalism.IrreducibleCountingLemmas.TW.sIdx (T n) (T (n + 1)) = ((relLen (T n) (T (n + 1))).toNat : ℤ)`. Unfold `Formalism.IrreducibleCountingLemmas.TW.sIdx`. Rewrite using `[h0]`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish `hall : ∀ n : ℕ, Formalism.IrreducibleCountingLemmas.TW.sIdx B (T 0) + n ≤ Formalism.IrreducibleCountingLemmas.TW.sIdx B (T n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih => have := hstep n`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Establish `h5` using `hall (C - Formalism.IrreducibleCountingLemmas.TW.sIdx B (T 0) + 1).toNat`. Establish `h6` using `hC _ (hT (C - Formalism.IrreducibleCountingLemmas.TW.sIdx B (T 0) + 1).toNat) le_sup_left`.

Establish `h7` using `Int.self_le_toNat (C - Formalism.IrreducibleCountingLemmas.TW.sIdx B (T 0) + 1)`. Use linear arithmetic over natural numbers and integers.
-/
theorem isLatIn_of_bound {B Y V : Submodule R W} (hB : IsLatIn B V) (hfg : Y.FG) (hYV : Y ≤ V) (C : ℤ)
    (hC : ∀ T : Submodule R W, IsLatIn T V → Y ≤ T → Formalism.IrreducibleCountingLemmas.TW.sIdx B T ≤ C) : IsLatIn Y V := by
  set m := IsLocalRing.maximalIdeal R with hm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖm : ϖ ∈ m := by rw [hm, hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
  have : IsNoetherian R B := isNoetherian_of_fg_of_noetherian B hB.1
  have fgle : ∀ N : Submodule R W, N ≤ B → N.FG := by
    intro N hN
    have h2 : (N.comap B.subtype).FG := IsNoetherian.noetherian _
    have h3 := h2.map B.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hN] at h3
  let Nn : ℕ → Submodule R W := fun n => (m ^ n) • B
  have hNB : ∀ n, Nn n ≤ B := fun n => Submodule.smul_le_right
  have hNlat : ∀ n, IsLatIn (Nn n) V := by
    intro n
    refine ⟨fgle _ (hNB n), (hNB n).trans hB.2.1, ?_⟩
    intro x hx
    obtain ⟨c, hc, h⟩ := hB.2.2 x hx
    refine ⟨ϖ ^ n * c, mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) hc, ?_⟩
    rw [mul_smul]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hϖm n) h
  let T : ℕ → Submodule R W := fun n => Y ⊔ Nn n
  have hT : ∀ n, IsLatIn (T n) V := fun n =>
    isLatIn_of_le (hNlat n) (hfg.sup (hNlat n).1) le_sup_right (sup_le hYV (hNlat n).2.1)
  by_cases hex : ∃ n, Nn n ≤ Y
  · obtain ⟨n, hn⟩ := hex
    exact isLatIn_of_le (hNlat n) hfg hn hYV
  · exfalso
    rw [not_exists] at hex
    have hsucc : ∀ n, Nn (n + 1) = m • Nn n := by
      intro n
      show (m ^ (n + 1)) • B = m • ((m ^ n) • B)
      rw [pow_succ', Submodule.mul_smul]
    have hle : ∀ n, T (n + 1) ≤ T n := by
      intro n
      refine sup_le_sup_left ?_ Y
      rw [hsucc]
      exact Submodule.smul_le_right
    have hne : ∀ n, ¬ T n ≤ T (n + 1) := by
      intro n h
      apply hex n
      have h1 : Nn n ≤ Y ⊔ m • Nn n := by
        rw [← hsucc]
        exact le_sup_right.trans h
      exact Submodule.le_of_le_smul_of_le_jacobson_bot (hNlat n).1
        (by rw [hm, IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) h1
    have hstep : ∀ n, Formalism.IrreducibleCountingLemmas.TW.sIdx B (T n) + 1 ≤ Formalism.IrreducibleCountingLemmas.TW.sIdx B (T (n + 1)) := by
      intro n
      have a := sIdx_add hB (hT n) (hT (n + 1))
      have h0 : relLen (T (n + 1)) (T n) = 0 := Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_of_le (hle n)
      have h1 : relLen (T n) (T (n + 1)) ≠ 0 := by
        unfold relLen
        rw [Ne, Module.length_eq_zero_iff]
        intro h
        refine hne n fun x hx => ?_
        have h9 := h.elim (Submodule.Quotient.mk (p := (T (n + 1)).comap (T n).subtype) ⟨x, hx⟩) 0
        rw [Submodule.Quotient.mk_eq_zero] at h9
        exact h9
      have h2 := relLen_ne_top (hT n) (hT (n + 1))
      have h3 : 1 ≤ (relLen (T n) (T (n + 1))).toNat := by
        obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 h2
        rw [← ha] at h1 ⊢
        simp only [ENat.toNat_natCast]
        have : a ≠ 0 := by rintro rfl; exact h1 rfl
        omega
      have h4 : Formalism.IrreducibleCountingLemmas.TW.sIdx (T n) (T (n + 1)) = ((relLen (T n) (T (n + 1))).toNat : ℤ) := by
        unfold Formalism.IrreducibleCountingLemmas.TW.sIdx
        rw [h0]; simp
      omega
    have hall : ∀ n : ℕ, Formalism.IrreducibleCountingLemmas.TW.sIdx B (T 0) + n ≤ Formalism.IrreducibleCountingLemmas.TW.sIdx B (T n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => have := hstep n; push_cast; omega
    have h5 := hall (C - Formalism.IrreducibleCountingLemmas.TW.sIdx B (T 0) + 1).toNat
    have h6 := hC _ (hT (C - Formalism.IrreducibleCountingLemmas.TW.sIdx B (T 0) + 1).toNat) le_sup_left
    have h7 := Int.self_le_toNat (C - Formalism.IrreducibleCountingLemmas.TW.sIdx B (T 0) + 1)
    omega

end More

end Idx

instance neZero_g (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

instance finite_levelGroup (N : NData D.R D.host D.what₂) : Finite (G0g N) := by
  unfold G0g
  infer_instance

/- English proof (translation)
Unfold `G0g`. Rewrite using `[Nat.card_pi, Fintype.prod_sigma, N.restN_card_levelGroup_eq]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) = _`. Rewrite using `[Finset.prod_const, Finset.card_univ, N.card_PlG]`.
-/
theorem natCard_codeWordStages_finiteGroup_eq (N : NData D.R D.host D.what₂) : Nat.card (G0g N) = D.what₂.restRowsFiniteGroupCard := by
  unfold G0g
  rw [Nat.card_pi, Fintype.prod_sigma, N.restN_card_levelGroup_eq]
  refine Finset.prod_congr rfl fun k _ => ?_
  show ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) = _
  rw [Finset.prod_const, Finset.card_univ, N.card_PlG]

def repG (i : X.Tw) (j : ℕ) (b : Bool) : Representation (FractionRing (X.O i)) (G0g N) (Y.Fm i j b) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem repG_apply (i : X.Tw) (j : ℕ) (b : Bool) (g : G0g N) (x : Y.Fm i j b) :
    repG Y i j b g x = Y.actG i j b g x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eG_eq (i : X.Tw) (j : ℕ) (b : Bool) : eG Y i j b = (repG Y i j b).asAlgebraHom (Y.eAlg i b) := rfl

/- English proof (translation)
Set `_ : Fintype (G0g N)` to `Fintype.ofFinite _`. Establish `hcard : Fintype.card (G0g N) = D.what₂.restRowsFiniteGroupCard`. Rewrite using `[← Nat.card_eq_fintype_card, natCard_codeWordStages_finiteGroup_eq]`. Establish `hint : ∀ g : G0g N, ∃ o : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) o = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) * (Y.eAlg i b).coeff g`. Introduce `g`.

Establish `h` using `Formalism.IrreducibleCountingLemmas.TW.central_idempotent_integral_twist (FractionRing (X.O i)) (G0g N) (Y.eAlg i b) (Y.eAlg_idem i b) (Y.eAlg_central i b) g`. Rewrite `h` using `[hcard]`. Establish `hO : IsIntegral (X.O i) (((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) * (Y.eAlg i b).coeff g)`. Take `⟨p, hp, he⟩` from `h`. Use `⟨p.map (Int.castRingHom (X.O i)), hp.map _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map]`. Conclude with `(congrArg (fun f => Polynomial.eval₂ f _ p) (RingHom.ext_int _ _)).trans he`. Conclude with `IsIntegrallyClosed.isIntegral_iff.1 hO`. Use `choose o ho using hint`. Use `⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm o), ?_⟩` and prove the remaining obligations.

Use extensionality with `g`. Simplify using `[MonoidAlgebra.coeff_map, ho]`.
-/
theorem eAlg_integral (i : X.Tw) (b : Bool) [CharZero (FractionRing (X.O i))] :
    ∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b := by
  classical
  let _ : Fintype (G0g N) := Fintype.ofFinite _
  have hcard : Fintype.card (G0g N) = D.what₂.restRowsFiniteGroupCard := by
    rw [← Nat.card_eq_fintype_card, natCard_codeWordStages_finiteGroup_eq]
  have hint : ∀ g : G0g N, ∃ o : X.O i, algebraMap (X.O i) (FractionRing (X.O i)) o =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) * (Y.eAlg i b).coeff g := by
    intro g
    have h := Formalism.IrreducibleCountingLemmas.TW.central_idempotent_integral_twist (FractionRing (X.O i)) (G0g N) (Y.eAlg i b)
      (Y.eAlg_idem i b) (Y.eAlg_central i b) g
    rw [hcard] at h
    have hO : IsIntegral (X.O i) (((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) * (Y.eAlg i b).coeff g) := by
      obtain ⟨p, hp, he⟩ := h
      refine ⟨p.map (Int.castRingHom (X.O i)), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact (congrArg (fun f => Polynomial.eval₂ f _ p) (RingHom.ext_int _ _)).trans he
    exact IsIntegrallyClosed.isIntegral_iff.1 hO
  choose o ho using hint
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm o), ?_⟩
  ext g
  simp [MonoidAlgebra.coeff_map, ho]

/- English proof (translation)
Rewrite using `[eG_eq, ← Module.End.mul_apply, ← map_mul, Y.eAlg_idem]`.
-/
theorem eG_idem (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    eG Y i j b (eG Y i j b x) = eG Y i j b x := by
  rw [eG_eq, ← Module.End.mul_apply, ← map_mul, Y.eAlg_idem]

/- English proof (translation)
Rewrite using `[← repG_apply, ← repG_apply, eG_eq, ← Representation.asAlgebraHom_single_one (repG Y i j b) g, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Y.eAlg_central]`.
-/
theorem eG_comm (i : X.Tw) (j : ℕ) (b : Bool) (g : G0g N) (x : Y.Fm i j b) :
    Y.actG i j b g (eG Y i j b x) = eG Y i j b (Y.actG i j b g x) := by
  rw [← repG_apply, ← repG_apply, eG_eq, ← Representation.asAlgebraHom_single_one (repG Y i j b) g,
    ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, Y.eAlg_central]

/- English proof (translation)
Rewrite using `[eG_eq, Formalism.IrreducibleCountingLemmas.TW.asAlgebraHom_apply_eq_sum]`. Conclude with `Submodule.sum_mem _ fun g _ => W.smul_mem _ (hW g x hx)`.
-/
theorem eG_mem (i : X.Tw) (j : ℕ) (b : Bool) (W : Submodule (FractionRing (X.O i)) (Y.Fm i j b))
    (hW : GStable Y i j b W) (x : Y.Fm i j b) (hx : x ∈ W) : eG Y i j b x ∈ W := by
  rw [eG_eq, Formalism.IrreducibleCountingLemmas.TW.asAlgebraHom_apply_eq_sum]
  exact Submodule.sum_mem _ fun g _ => W.smul_mem _ (hW g x hx)

/- English proof (translation)
Take `⟨_, hst, hirr⟩` from `hW`. Establish `hle : W.map (eG Y i j b) ≤ W`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `eG_mem Y i j b W hst x hx`. Establish `hst' : GStable Y i j b (W.map (eG Y i j b))`.

Introduce and unpack `g _ ⟨x, hx, rfl⟩`. Conclude with `⟨Y.actG i j b g x, hst g x hx, (eG_comm Y i j b g x).symm⟩`. Break down `hirr _ hle hst' with h | h` into its components or cases. Use `right`. Introduce `x hx`.

Establish `: eG Y i j b x ∈ W.map (eG Y i j b)` using `⟨x, hx, rfl⟩`. Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot _).1 this`. Use `left`. Introduce `x hx`.

Rewrite `hx` using `[← h]`. Take `⟨y, _, rfl⟩` from `hx`. Conclude with `eG_idem Y i j b y`.
-/
theorem eG_irred (i : X.Tw) (j : ℕ) (b : Bool) (W : Submodule (FractionRing (X.O i)) (Y.Fm i j b))
    (hW : GIrred Y i j b W) : (∀ x ∈ W, eG Y i j b x = x) ∨ (∀ x ∈ W, eG Y i j b x = 0) := by
  obtain ⟨_, hst, hirr⟩ := hW
  have hle : W.map (eG Y i j b) ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact eG_mem Y i j b W hst x hx
  have hst' : GStable Y i j b (W.map (eG Y i j b)) := by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨Y.actG i j b g x, hst g x hx, (eG_comm Y i j b g x).symm⟩
  rcases hirr _ hle hst' with h | h
  · right
    intro x hx
    have : eG Y i j b x ∈ W.map (eG Y i j b) := ⟨x, hx, rfl⟩
    rw [h] at this
    exact (Submodule.mem_bot _).1 this
  · left
    intro x hx
    rw [← h] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact eG_idem Y i j b y

def HeckeCommutesLevelGroup : Prop :=
  ∀ (i : X.Tw), X.NonzeroIndexPlace i → ∀ (b : Bool), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g k P, HkIdx i k P →
    (Y.actG i j b g).toLinearMap ∘ₗ Y.hkF i j b k P = Y.hkF i j b k P ∘ₗ (Y.actG i j b g).toLinearMap

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i hi b j hj`. Conclude with `((h i hi b).2 j hj).1`. Introduce `h i hi b`. Conclude with `⟨eAlg_integral Y i b, fun j hj => ⟨h i hi b j hj, fun _ W _ hW => eG_irred Y i j b W hW⟩⟩`.
-/
theorem admissibleGoodIdempotent_iff_reduced [∀ i : X.Tw, CharZero (FractionRing (X.O i))] : GroupAlgebraIntegrality Y ↔ HeckeCommutesLevelGroup Y := by
  constructor
  · intro h i hi b j hj
    exact ((h i hi b).2 j hj).1
  · intro h i hi b
    exact ⟨eAlg_integral Y i b, fun j hj => ⟨h i hi b j hj, fun _ W _ hW => eG_irred Y i j b W hW⟩⟩

/- English proof (translation)
Unfold `Fm0`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]`.
-/
theorem mem_typeSubspace_iff_unipotent_character {i : X.Tw} {j : ℕ} {b : Bool} (x : Y.Fm i j b) :
    x ∈ Fm0 Y i j b ↔ ∀ u : Y.U, Y.actG i j b u x =
      ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • x := by
  unfold Fm0
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, LinearEquiv.coe_coe]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_typeSubspace_iff_unipotent_character]`. Introduce `u`. Rewrite using `[eG_comm, hx u, map_smul]`.
-/
theorem idempotent_preserves_forms {i : X.Tw} {j : ℕ} {b : Bool} {x : Y.Fm i j b} (hx : x ∈ Fm0 Y i j b) :
    eG Y i j b x ∈ Fm0 Y i j b := by
  rw [mem_typeSubspace_iff_unipotent_character] at hx ⊢
  intro u
  rw [eG_comm, hx u, map_smul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨idempotent_preserves_forms Y hy, eG_idem Y i j b y⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨x, h1, h2⟩`.
-/
theorem mem_invariant_forms {i : X.Tw} {j : ℕ} {b : Bool} (x : Y.Fm i j b) :
    x ∈ V0 Y i j b ↔ x ∈ Fm0 Y i j b ∧ eG Y i j b x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨idempotent_preserves_forms Y hy, eG_idem Y i j b y⟩
  · rintro ⟨h1, h2⟩
    exact ⟨x, h1, h2⟩

/- English proof (translation)
Use `show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x = _`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`.
-/
theorem AO_apply (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • eG Y i j b x := by
  show ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) • eG Y i j b x = _
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Rewrite using `[AO_apply, map_smul, LinearMap.smul_apply, eG_eq]`.
-/
theorem AO_eq_asAlgebraHom (i : X.Tw) (j : ℕ) (b : Bool) (x : Y.Fm i j b) :
    AO Y i j b x = (repG Y i j b).asAlgebraHom
      (((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b) x := by
  rw [AO_apply, map_smul, LinearMap.smul_apply, eG_eq]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[AO_eq_asAlgebraHom, ← hc]`. Both sides reduce to the same expression.
-/
theorem zO_eq_AO (i : X.Tw) (j : ℕ) (b : Bool) (c : MonoidAlgebra (X.O i) (G0g N))
    (hc : MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b) :
    zO Y i j b c = AO Y i j b := by
  ext x
  rw [AO_eq_asAlgebraHom, ← hc]
  rfl

/- English proof (translation)
The claim follows from `Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'`.
-/
theorem card_ne_zero (i : X.Tw) [CharZero (FractionRing (X.O i))] :
    ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) ≠ 0 :=
  Nat.cast_ne_zero.2 D.what₂.restRowsFiniteGroupCard_pos.ne'

/- English proof (translation)
Set `_ : Fintype (G0g N)` to `Fintype.ofFinite _`. Establish `hcard : Fintype.card (G0g N) = D.what₂.restRowsFiniteGroupCard`. Rewrite using `[← Nat.card_eq_fintype_card, natCard_codeWordStages_finiteGroup_eq]`. Establish `hxF : x ∈ Fm0 Y i j b` using `hx.2`. Establish `cut` using `Formalism.IrreducibleCountingLemmas.TW.truncation_operator_holds (X.O i) (FractionRing (X.O i)) (G0g N) (Y.Fm i j b) (repG Y i j b) (Y.Bsup i j b) Y.U (Y.psiU i b) (Y.eAlg i b) (fun g v hv => hst g ⟨v, hv, rfl⟩) (Y.eAlg_idem i b) (Y.eAlg_central i b) x hx.1 ((mem_typeSubspace_iff …`.

Rewrite `cut` using `[hcard, ← AO_eq_asAlgebraHom]`. Establish `hF : AO Y i j b x ∈ Fm0 Y i j b` using `(mem_typeSubspace_iff_unipotent_character Y _).2 cut.2.1`. Conclude with `⟨⟨cut.1, hF⟩, (mem_invariant_forms Y _).2 ⟨hF, cut.2.2.1⟩⟩`.
-/
theorem AO_cut (i : X.Tw) (j : ℕ) (b : Bool) [CharZero (FractionRing (X.O i))]
    (hst : ∀ g, (Y.Bsup i j b).map ((Y.actG i j b g).toLinearMap.restrictScalars (X.O i)) ≤ Y.Bsup i j b)
    (x : Y.Fm i j b) (hx : x ∈ Mall Y i j b) :
    AO Y i j b x ∈ Mall Y i j b ∧ AO Y i j b x ∈ V0 Y i j b := by
  classical
  let _ : Fintype (G0g N) := Fintype.ofFinite _
  have hcard : Fintype.card (G0g N) = D.what₂.restRowsFiniteGroupCard := by
    rw [← Nat.card_eq_fintype_card, natCard_codeWordStages_finiteGroup_eq]
  have hxF : x ∈ Fm0 Y i j b := hx.2
  have cut := Formalism.IrreducibleCountingLemmas.TW.truncation_operator_holds (X.O i) (FractionRing (X.O i)) (G0g N) (Y.Fm i j b)
    (repG Y i j b) (Y.Bsup i j b) Y.U (Y.psiU i b) (Y.eAlg i b)
    (fun g v hv => hst g ⟨v, hv, rfl⟩) (Y.eAlg_idem i b) (Y.eAlg_central i b) x hx.1
    ((mem_typeSubspace_iff_unipotent_character Y x).1 hxF)
  rw [hcard, ← AO_eq_asAlgebraHom] at cut
  have hF : AO Y i j b x ∈ Fm0 Y i j b := (mem_typeSubspace_iff_unipotent_character Y _).2 cut.2.1
  exact ⟨⟨cut.1, hF⟩, (mem_invariant_forms Y _).2 ⟨hF, cut.2.2.1⟩⟩

/- English proof (translation)
Rewrite using `[eG_eq, Formalism.IrreducibleCountingLemmas.TW.asAlgebraHom_apply_eq_sum, Formalism.IrreducibleCountingLemmas.TW.asAlgebraHom_apply_eq_sum, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Use `congr 1`. Conclude with `LinearMap.congr_fun (hT g) x`.
-/
theorem eG_commT (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hT : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) (x : Y.Fm i j b) :
    eG Y i j b (T x) = T (eG Y i j b x) := by
  rw [eG_eq, Formalism.IrreducibleCountingLemmas.TW.asAlgebraHom_apply_eq_sum, Formalism.IrreducibleCountingLemmas.TW.asAlgebraHom_apply_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul]
  congr 1
  exact LinearMap.congr_fun (hT g) x

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_typeSubspace_iff_unipotent_character]`. Introduce `u`. Use `LinearMap.congr_fun (hT u) x` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this`. Rewrite using `[this, hx u, map_smul]`.
-/
theorem commuting_endomorphism_preserves_forms (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hT : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) {x : Y.Fm i j b}
    (hx : x ∈ Fm0 Y i j b) : T x ∈ Fm0 Y i j b := by
  rw [mem_typeSubspace_iff_unipotent_character] at hx ⊢
  intro u
  have := LinearMap.congr_fun (hT u) x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
  rw [this, hx u, map_smul]

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_invariant_forms]`. Conclude with `⟨commuting_endomorphism_preserves_forms Y i j b T hT hx.1, by rw [eG_commT Y i j b T hT, hx.2]⟩`.
-/
theorem commuting_endomorphism_preserves_invariants (i : X.Tw) (j : ℕ) (b : Bool) (T : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hT : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ T = T ∘ₗ (Y.actG i j b g).toLinearMap) {x : Y.Fm i j b}
    (hx : x ∈ V0 Y i j b) : T x ∈ V0 Y i j b := by
  rw [mem_invariant_forms] at hx ⊢
  exact ⟨commuting_endomorphism_preserves_forms Y i j b T hT hx.1, by rw [eG_commT Y i j b T hT, hx.2]⟩

def expFam (i : X.Tw) (c : Bool → MonoidAlgebra (X.O i) (G0g N))
    (S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b)) : RFam Y i where
  Ball := fun j b => Mall Y i j b
  z := fun _ b => c b
  B := fun j b => Mall Y i j b ⊓ (V0 Y i j b).restrictScalars (X.O i)
  S := S

section Lat

open Formalism.IrreducibleCountingLemmas

/- English proof (translation)
Unfold `TW.relLen`. Use `(LinearEquiv.length_eq ?_).symm` and prove the remaining obligations. Use `Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf M) ?_` and prove the remaining obligations. Use extensionality with `⟨y, hy⟩`. Simplify using `only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨x, hx⟩, hxN, hxy⟩`. Conclude with `⟨x, hxN, congrArg Subtype.val hxy⟩`. Introduce and unpack `⟨x, hxN, rfl⟩`. Take `⟨x', hx', hxx⟩` from `hy`.

Establish `: x' = x` using `hf hxx`. Substitute `this` using the available equality. Conclude with `⟨⟨x', hx'⟩, hxN, rfl⟩`.
-/
theorem relLen_map {R U₁ U₂ : Type} [CommRing R] [AddCommGroup U₁] [Module R U₁] [AddCommGroup U₂]
    [Module R U₂] (f : U₁ →ₗ[R] U₂) (hf : Function.Injective f) (M N' : Submodule R U₁) :
    TW.relLen (M.map f) (N'.map f) = TW.relLen M N' := by
  unfold TW.relLen
  refine (LinearEquiv.length_eq ?_).symm
  refine Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf M) ?_
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hx⟩, hxN, hxy⟩
    exact ⟨x, hxN, congrArg Subtype.val hxy⟩
  · rintro ⟨x, hxN, rfl⟩
    obtain ⟨x', hx', hxx⟩ := hy
    have : x' = x := hf hxx
    subst this
    exact ⟨⟨x', hx'⟩, hxN, rfl⟩

/- English proof (translation)
Unfold `TW.sIdx`. Rewrite using `[relLen_map f hf, relLen_map f hf]`.
-/
theorem sIdxTW_map {R U₁ U₂ : Type} [CommRing R] [AddCommGroup U₁] [Module R U₁] [AddCommGroup U₂]
    [Module R U₂] (f : U₁ →ₗ[R] U₂) (hf : Function.Injective f) (M N' : Submodule R U₁) :
    TW.sIdx (M.map f) (N'.map f) = TW.sIdx M N' := by
  unfold TW.sIdx
  rw [relLen_map f hf, relLen_map f hf]

/- English proof (translation)
Unfold `TW.scaleLat`. Rewrite using `[← Submodule.map_comp, ← Submodule.map_comp]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem scaleLat_map {R U₁ U₂ : Type} [CommRing R] [AddCommGroup U₁] [Module R U₁] [AddCommGroup U₂]
    [Module R U₂] (f : U₁ →ₗ[R] U₂) (c : R) (N' : Submodule R U₁) :
    TW.scaleLat c (N'.map f) = (TW.scaleLat c N').map f := by
  unfold TW.scaleLat
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp

/- English proof (translation)
Unfold `sIdx lenR TW.sIdx TW.relLen`. Use `push_cast`. Rewrite using `[sub_div]`.
-/
theorem sIdx_eq {R W : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup W]
    [Module R W] (l : ℕ) (M N' : Submodule R W) :
    sIdx l M N' = (TW.sIdx M N' : ℝ) / ((IsDiscreteValuationRing.addVal R (l : R)).toNat : ℝ) := by
  unfold sIdx lenR TW.sIdx TW.relLen
  push_cast
  rw [sub_div]

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {U : Type} [AddCommGroup U]
  [Module R U]

abbrev LocV (V : Submodule R U) : Type := LocalizedModule (nonZeroDivisors R) ↥V

def toLoc (V : Submodule R U) : ↥V →ₗ[R] LocV V := LocalizedModule.mkLinearMap (nonZeroDivisors R) ↥V

instance isLoc_toLoc (V : Submodule R U) : IsLocalizedModule (nonZeroDivisors R) (toLoc V) :=
  inferInstanceAs (IsLocalizedModule (nonZeroDivisors R)
    (LocalizedModule.mkLinearMap (nonZeroDivisors R) ↥V))

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨c, hc⟩` from `(IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) (toLoc V)).1 hx`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hU c x (nonZeroDivisors.ne_zero c.2) (congrArg Subtype.val hc)`.
-/
theorem toLoc_inj (V : Submodule R U) (hU : ∀ (r : R) (x : U), r ≠ 0 → r • x = 0 → x = 0) :
    Function.Injective (toLoc V) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) (toLoc V)).1 hx
  apply Subtype.ext
  exact hU c x (nonZeroDivisors.ne_zero c.2) (congrArg Subtype.val hc)

def inLoc (V M : Submodule R U) : Submodule R (LocV V) := (M.comap V.subtype).map (toLoc V)

/- English proof (translation)
Unfold `inLoc`. Rewrite using `[sIdxTW_map _ (toLoc_inj V hU), ← sIdxTW_map V.subtype V.injective_subtype, Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hM, inf_eq_right.2 hN]`.
-/
theorem sIdx_inLoc (V : Submodule R U) (hU : ∀ (r : R) (x : U), r ≠ 0 → r • x = 0 → x = 0)
    (M N' : Submodule R U) (hM : M ≤ V) (hN : N' ≤ V) :
    TW.sIdx (inLoc V M) (inLoc V N') = TW.sIdx M N' := by
  unfold inLoc
  rw [sIdxTW_map _ (toLoc_inj V hU), ← sIdxTW_map V.subtype V.injective_subtype,
    Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hM, inf_eq_right.2 hN]

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `V.smul_mem c (hN hx)`.
-/
theorem scaleLat_le (V N' : Submodule R U) (c : R) (hN : N' ≤ V) : TW.scaleLat c N' ≤ V := by
  rintro _ ⟨x, hx, rfl⟩
  exact V.smul_mem c (hN hx)

/- English proof (translation)
Unfold `inLoc`. Rewrite using `[scaleLat_map]`. Use `congr 1`. Apply `Submodule.map_injective_of_injective V.injective_subtype` to reduce the goal to its premises. Rewrite using `[← scaleLat_map, Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hN, inf_eq_right.2 (scaleLat_le V N' c hN)]`.
-/
theorem scaleLat_inLoc (V N' : Submodule R U) (c : R) (hN : N' ≤ V) :
    TW.scaleLat c (inLoc V N') = inLoc V (TW.scaleLat c N') := by
  unfold inLoc
  rw [scaleLat_map]
  congr 1
  apply Submodule.map_injective_of_injective V.injective_subtype
  rw [← scaleLat_map, Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hN,
    inf_eq_right.2 (scaleLat_le V N' c hN)]

/- English proof (translation)
Take `⟨hfg, hle, hfull⟩` from `hM`. Prove the components needed by the constructor for the conclusion. Apply `Submodule.FG.map` to reduce the goal to its premises. Apply `Submodule.fg_of_fg_map_injective V.subtype V.injective_subtype` to reduce the goal to its premises. Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.2 hle]`.

Conclude with `hfg`. Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨⟨m, t⟩, hmt⟩` from `IsLocalizedModule.surj (nonZeroDivisors R) (toLoc V) y`. Take `⟨c, hc, hcm⟩` from `hfull m m.2`.

Establish `hne : algebraMap R (FractionRing R) (c * t) ≠ 0`. Simplify using `using mul_ne_zero hc (nonZeroDivisors.ne_zero t.2)`. Establish `h1 : (c * (t : R)) • y = toLoc V (c • m)`. Rewrite using `[mul_smul, map_smul]`. Use `congr 1`.

Establish `h2 : toLoc V (c • m) ∈ inLoc V M` using `⟨c • m, hcm, rfl⟩`. Establish `h3 : y = (algebraMap R (FractionRing R) (c * t))⁻¹ • ((c * (t : R)) • y)`. Rewrite using `[← algebraMap_smul (FractionRing R) (c * (t : R)) y, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Rewrite using `[h3, h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span h2)`.
-/
theorem isLat_inLoc (V M : Submodule R U) (hM : IsLatIn M V) :
    TW.IsLat R (FractionRing R) (inLoc V M) := by
  obtain ⟨hfg, hle, hfull⟩ := hM
  constructor
  · apply Submodule.FG.map
    apply Submodule.fg_of_fg_map_injective V.subtype V.injective_subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hle]
    exact hfg
  · rw [eq_top_iff]
    intro y _
    obtain ⟨⟨m, t⟩, hmt⟩ := IsLocalizedModule.surj (nonZeroDivisors R) (toLoc V) y
    obtain ⟨c, hc, hcm⟩ := hfull m m.2
    have hne : algebraMap R (FractionRing R) (c * t) ≠ 0 := by
      simpa using mul_ne_zero hc (nonZeroDivisors.ne_zero t.2)
    have h1 : (c * (t : R)) • y = toLoc V (c • m) := by
      rw [mul_smul, map_smul]
      congr 1
    have h2 : toLoc V (c • m) ∈ inLoc V M := ⟨c • m, hcm, rfl⟩
    have h3 : y = (algebraMap R (FractionRing R) (c * t))⁻¹ • ((c * (t : R)) • y) := by
      rw [← algebraMap_smul (FractionRing R) (c * (t : R)) y, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h3, h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h2)

/- English proof (translation)
Take `⟨⟨t, ht⟩, hspan⟩` from `isLat_inLoc V M hM`. Use `⟨⟨t, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hspan, ← ht, Submodule.span_span_of_tower]`.
-/
theorem finDim_LocV (V M : Submodule R U) (hM : IsLatIn M V) :
    FiniteDimensional (FractionRing R) (LocV V) := by
  obtain ⟨⟨t, ht⟩, hspan⟩ := isLat_inLoc V M hM
  refine ⟨⟨t, ?_⟩⟩
  rw [← hspan, ← ht, Submodule.span_span_of_tower]

/- English proof (translation)
Rewrite `h`, the goal using `[sIdx_eq, sIdx_eq]`. Break down `Nat.eq_zero_or_pos (IsDiscreteValuationRing.addVal R (l : R)).toNat with he | he` into its components or cases. Rewrite using `[he]`. Simplify using `using hε`. Use `finDim_LocV V M hM` as an intermediate fact.

Establish `key` using `TW.export_transfer_holds R (FractionRing R) (LocV V) (inLoc V M) (inLoc V B) (inLoc V N') (inLoc V N'') c _ ε (isLat_inLoc V M hM) (isLat_inLoc V B hB) (isLat_inLoc V N' hN) (isLat_inLoc V N'' hN') hc he`. Rewrite `key` using `[scaleLat_inLoc V N'' c hN'.2.1, scaleLat_inLoc V N' c hN.2.1, sIdx_inLoc V hU _ _ hB.2.1 (scaleLat_le V N'' c hN'.2.1), sIdx_inLoc V hU _ _ hB.2.1 (scaleLat_le V N' c hN.2.1), sIdx_inLoc V hU _ _ hM.2.1 hN'.2.1, sIdx_inLoc V hU _ _ hM.2.1 hN.2.1]`. Conclude with `key h`.
-/
theorem exportTransfer_mod (hU : ∀ (r : R) (x : U), r ≠ 0 → r • x = 0 → x = 0) (l : ℕ)
    (V M B N' N'' : Submodule R U) (c : R) (ε : ℝ) (hε : 0 ≤ ε) (hM : IsLatIn M V) (hB : IsLatIn B V)
    (hN : IsLatIn N' V) (hN' : IsLatIn N'' V) (hc : c ≠ 0)
    (h : sIdx l B (TW.scaleLat c N'') ≤ sIdx l B (TW.scaleLat c N') + ε) :
    sIdx l M N'' ≤ sIdx l M N' + ε := by
  rw [sIdx_eq, sIdx_eq] at h ⊢
  rcases Nat.eq_zero_or_pos (IsDiscreteValuationRing.addVal R (l : R)).toNat with he | he
  · rw [he]; simpa using hε
  have := finDim_LocV V M hM
  have key := TW.export_transfer_holds R (FractionRing R) (LocV V) (inLoc V M) (inLoc V B) (inLoc V N')
    (inLoc V N'') c _ ε (isLat_inLoc V M hM) (isLat_inLoc V B hB) (isLat_inLoc V N' hN)
    (isLat_inLoc V N'' hN') hc he
  rw [scaleLat_inLoc V N'' c hN'.2.1, scaleLat_inLoc V N' c hN.2.1,
    sIdx_inLoc V hU _ _ hB.2.1 (scaleLat_le V N'' c hN'.2.1),
    sIdx_inLoc V hU _ _ hB.2.1 (scaleLat_le V N' c hN.2.1),
    sIdx_inLoc V hU _ _ hM.2.1 hN'.2.1, sIdx_inLoc V hU _ _ hM.2.1 hN.2.1] at key
  exact key h

end Lat

section BC

open Formalism.IrreducibleCountingLemmas

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x h => exact hs x h`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨c, hc, hcx⟩` from `hx`. Take `⟨d, hd, hdy⟩` from `hy`. Use `⟨c * d, mul_ne_zero hc hd, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `N'.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `N'.smul_mem d hcx`. Rewrite using `[mul_smul]`. Conclude with `N'.smul_mem c hdy`. Consider the case `smul a x _ hx`.

Take `⟨c, hc, hcx⟩` from `hx`. Conclude with `⟨c, hc, by rw [smul_comm]; exact N'.smul_mem a hcx⟩`.
-/
theorem full_span {R U : Type*} [CommRing R] [IsDomain R] [AddCommGroup U] [Module R U]
    (N' : Submodule R U) (s : Set U) (hs : ∀ x ∈ s, ∃ c : R, c ≠ 0 ∧ c • x ∈ N') :
    ∀ x ∈ Submodule.span R s, ∃ c : R, c ≠ 0 ∧ c • x ∈ N' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact hs x h
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdy⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine N'.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N'.smul_mem d hcx
    · rw [mul_smul]; exact N'.smul_mem c hdy
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    exact ⟨c, hc, by rw [smul_comm]; exact N'.smul_mem a hcx⟩

/- English proof (translation)
Unfold `TW.scaleLat`. Rewrite using `[← Submodule.map_comp]`. Use `congr 1`.
-/
theorem map_smul_eq_scaleLat {R U₁ U₂ : Type} [CommRing R] [AddCommGroup U₁] [Module R U₁]
    [AddCommGroup U₂] [Module R U₂] (c : R) (f : U₁ →ₗ[R] U₂) (P : Submodule R U₁) :
    P.map (c • f) = TW.scaleLat c (P.map f) := by
  unfold TW.scaleLat
  rw [← Submodule.map_comp]
  congr 1

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `P.smul_mem c hx`.
-/
theorem scaleLat_le_self {R U : Type} [CommRing R] [AddCommGroup U] [Module R U] (c : R)
    (P : Submodule R U) : TW.scaleLat c P ≤ P := by
  rintro _ ⟨x, hx, rfl⟩
  exact P.smul_mem c hx

/- English proof (translation)
Use `⟨Submodule.fg_of_fg_map_injective (LinearMap.lsmul R U c) ?_ h.1, hP, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Conclude with `fun x hx => hU c x hc hx`. Take `⟨d, hd, hdx⟩` from `h.2.2 x hx`. Conclude with `⟨d, hd, scaleLat_le_self c P hdx⟩`.
-/
theorem isLatIn_of_scale {R U : Type} [CommRing R] [AddCommGroup U] [Module R U]
    (hU : ∀ (r : R) (x : U), r ≠ 0 → r • x = 0 → x = 0) (c : R) (hc : c ≠ 0) (P V : Submodule R U)
    (hP : P ≤ V) (h : IsLatIn (TW.scaleLat c P) V) : IsLatIn P V := by
  refine ⟨Submodule.fg_of_fg_map_injective (LinearMap.lsmul R U c) ?_ h.1, hP, fun x hx => ?_⟩
  · rw [injective_iff_map_eq_zero]
    exact fun x hx => hU c x hc hx
  · obtain ⟨d, hd, hdx⟩ := h.2.2 x hx
    exact ⟨d, hd, scaleLat_le_self c P hdx⟩

variable {O : Type} [CommRing O] [IsDomain O] {W : Type} [AddCommGroup W] [Module O W]
  [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W]

/- English proof (translation)
Establish `hr' : algebraMap O (FractionRing O) r ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hr`. Rewrite `h` using `[← algebraMap_smul (FractionRing O) r x]`. Conclude with `(smul_eq_zero.1 h).resolve_left hr'`.
-/
theorem tf_space (r : O) (x : W) (hr : r ≠ 0) (h : r • x = 0) : x = 0 := by
  have hr' : algebraMap O (FractionRing O) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hr
  rw [← algebraMap_smul (FractionRing O) r x] at h
  exact (smul_eq_zero.1 h).resolve_left hr'

/- English proof (translation)
Take `⟨d, hd, r', hr'⟩` from `(Algebra.IsIntegral.isIntegral (R := O) r).isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hr)`. Establish `h1 : d • x = 0`. Rewrite using `[← algebraMap_smul O' d x, hr', mul_comm, mul_smul, h, smul_zero]`. Establish `hd' : algebraMap O (FractionRing O) d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd`. Set `g : W →ₗ[O] W` to `((algebraMap O (FractionRing O) d)⁻¹ • (LinearMap.id : W →ₗ[FractionRing O] W)).restrictScalars O`.

Establish `hg : d • g = LinearMap.id`. Use extensionality with `w`. Use `show d • ((algebraMap O (FractionRing O) d)⁻¹ • w) = w`. Rewrite using `[← algebraMap_smul (FractionRing O) d, smul_smul, mul_inv_cancel₀ hd', one_smul]`. Establish `: x = g.lTensor O' (d • x)`.

Rewrite using `[map_smul, ← LinearMap.smul_apply, ← LinearMap.lTensor_smul, hg, LinearMap.lTensor_id, LinearMap.id_apply]`. Rewrite using `[this, h1, map_zero]`.
-/
theorem tf_tensor {O' : Type} [CommRing O'] [IsDomain O'] [Algebra O O'] [Algebra.IsIntegral O O']
    (r : O') (x : O' ⊗[O] W) (hr : r ≠ 0) (h : r • x = 0) : x = 0 := by
  obtain ⟨d, hd, r', hr'⟩ := (Algebra.IsIntegral.isIntegral (R := O) r).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hr)
  have h1 : d • x = 0 := by
    rw [← algebraMap_smul O' d x, hr', mul_comm, mul_smul, h, smul_zero]
  have hd' : algebraMap O (FractionRing O) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd
  let g : W →ₗ[O] W :=
    ((algebraMap O (FractionRing O) d)⁻¹ • (LinearMap.id : W →ₗ[FractionRing O] W)).restrictScalars O
  have hg : d • g = LinearMap.id := by
    ext w
    show d • ((algebraMap O (FractionRing O) d)⁻¹ • w) = w
    rw [← algebraMap_smul (FractionRing O) d, smul_smul, mul_inv_cancel₀ hd', one_smul]
  have : x = g.lTensor O' (d • x) := by
    rw [map_smul, ← LinearMap.smul_apply, ← LinearMap.lTensor_smul, hg, LinearMap.lTensor_id,
      LinearMap.id_apply]
  rw [this, h1, map_zero]

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
Rewrite using `[Submodule.baseChange_eq_span, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `Submodule.tmul_mem_baseChange_of_mem 1 (h hx)`.
-/
theorem baseChange_mono' (O' : Type) [CommRing O'] [Algebra O O'] {P V : Submodule O W} (h : P ≤ V) :
    P.baseChange O' ≤ V.baseChange O' := by
  rw [Submodule.baseChange_eq_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Submodule.tmul_mem_baseChange_of_mem 1 (h hx)

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
Rewrite using `[Submodule.baseChange_eq_span, Submodule.map_span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[TensorProduct.mk_apply, LinearMap.baseChange_tmul]`. Conclude with `Submodule.tmul_mem_baseChange_of_mem 1 (h ⟨x, hx, rfl⟩)`.
-/
theorem map_baseChange_le (O' : Type) [CommRing O'] [Algebra O O'] {P V : Submodule O W}
    (f : W →ₗ[O] W) (h : P.map f ≤ V) : (P.baseChange O').map (f.baseChange O') ≤ V.baseChange O' := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span_le]
  rintro _ ⟨x, hx, rfl⟩
  rw [TensorProduct.mk_apply, LinearMap.baseChange_tmul]
  exact Submodule.tmul_mem_baseChange_of_mem 1 (h ⟨x, hx, rfl⟩)

omit [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
Take `⟨⟨t, ht⟩, hle, hfull⟩` from `h`. Use `⟨?_, baseChange_mono' O' hle, ?_⟩` and prove the remaining obligations. Rewrite using `[← ht, Submodule.baseChange_span]`. Conclude with `Submodule.fg_span (t.finite_toSet.image _)`. Rewrite using `[Submodule.baseChange_eq_span O' V]`.

Apply `full_span` to reduce the goal to its premises. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Take `⟨c, hc, hcv⟩` from `hfull v hv`. Use `⟨algebraMap O O' c, (map_ne_zero_iff _ hinj).2 hc, ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.mk_apply, algebraMap_smul, ← TensorProduct.tmul_smul]`.

Conclude with `Submodule.tmul_mem_baseChange_of_mem 1 hcv`.
-/
theorem isLatIn_baseChange (O' : Type) [CommRing O'] [IsDomain O'] [Algebra O O']
    (hinj : Function.Injective (algebraMap O O')) (P V : Submodule O W) (h : IsLatIn P V) :
    IsLatIn (P.baseChange O') (V.baseChange O') := by
  obtain ⟨⟨t, ht⟩, hle, hfull⟩ := h
  refine ⟨?_, baseChange_mono' O' hle, ?_⟩
  · rw [← ht, Submodule.baseChange_span]
    exact Submodule.fg_span (t.finite_toSet.image _)
  · rw [Submodule.baseChange_eq_span O' V]
    apply full_span
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨c, hc, hcv⟩ := hfull v hv
    refine ⟨algebraMap O O' c, (map_ne_zero_iff _ hinj).2 hc, ?_⟩
    rw [TensorProduct.mk_apply, algebraMap_smul, ← TensorProduct.tmul_smul]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hcv

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
Unfold `TW.scaleLat`. Rewrite using `[Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Use `⟨(1 : O') ⊗ₜ[O] x, ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Use `⟨c • x, ⟨x, hx, rfl⟩, ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem scaleLat_baseChange (O' : Type) [CommRing O'] [Algebra O O'] (c : O) (P : Submodule O W) :
    (TW.scaleLat c P).baseChange O' = TW.scaleLat (algebraMap O O' c) (P.baseChange O') := by
  unfold TW.scaleLat
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(1 : O') ⊗ₜ[O] x, ⟨x, hx, rfl⟩, ?_⟩
    simp
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨c • x, ⟨x, hx, rfl⟩, ?_⟩
    simp

variable {Ok O' : Type} [CommRing Ok] [CommRing O'] [Algebra O Ok] [Algebra O O'] [Algebra Ok O']
  [IsScalarTower O Ok O']

variable (O W Ok O') in

abbrev rho : Ok ⊗[O] W →ₗ[O] O' ⊗[O] W :=
  LinearMap.rTensor W (IsScalarTower.toAlgHom O Ok O').toLinearMap

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b w => simp [TensorProduct.smul_tmul', Algebra.smul_def]`. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`.
-/
theorem rho_smul (a : Ok) (x : Ok ⊗[O] W) :
    rho O W Ok O' (a • x) = algebraMap Ok O' a • rho O W Ok O' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b w => simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (O') in

def up (T : Submodule Ok (Ok ⊗[O] W)) : Submodule O' (O' ⊗[O] W) :=
  Submodule.span O' (rho O W Ok O' '' (T : Set (Ok ⊗[O] W)))

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `up`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul a x _ hx => rw [rho_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem up_span (t : Set (Ok ⊗[O] W)) :
    up O' (Submodule.span Ok t) = Submodule.span O' (rho O W Ok O' '' t) := by
  apply le_antisymm
  · unfold up
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x h => exact Submodule.subset_span ⟨x, h, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [rho_smul]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono h)`.
-/
theorem up_mono {T T' : Submodule Ok (Ok ⊗[O] W)} (h : T ≤ T') : up O' T ≤ up O' T' :=
  Submodule.span_mono (Set.image_mono h)

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
Rewrite using `[Submodule.baseChange_eq_span, up_span, Submodule.baseChange_eq_span]`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`.

Conclude with `⟨x, hx, by simp⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨(1 : Ok) ⊗ₜ[O] x, ⟨x, hx, rfl⟩, by simp⟩`.
-/
theorem up_baseChange (P : Submodule O W) : up O' (P.baseChange Ok) = P.baseChange O' := by
  rw [Submodule.baseChange_eq_span, up_span, Submodule.baseChange_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(1 : Ok) ⊗ₜ[O] x, ⟨x, hx, rfl⟩, by simp⟩

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
Unfold `TW.scaleLat up`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨rho O W Ok O' x, ⟨x, hx, rfl⟩, by simp [rho_smul]⟩`. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨a • x, ⟨x, hx, rfl⟩, by simp [rho_smul]⟩`.
-/
theorem up_scaleLat (a : Ok) (T : Submodule Ok (Ok ⊗[O] W)) :
    up O' (TW.scaleLat a T) = TW.scaleLat (algebraMap Ok O' a) (up O' T) := by
  unfold TW.scaleLat up
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨rho O W Ok O' x, ⟨x, hx, rfl⟩, by simp [rho_smul]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨x, hx, rfl⟩, by simp [rho_smul]⟩

omit [IsDomain O] [Module (FractionRing O) W] [IsScalarTower O (FractionRing O) W] in
/- English proof (translation)
Take `⟨⟨t, ht⟩, hle, hfull⟩` from `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← ht, up_span]`. Conclude with `Submodule.fg_span (t.finite_toSet.image _)`. Rewrite using `[← up_baseChange (Ok := Ok) (O' := O') V]`.

Conclude with `up_mono hle`. Rewrite using `[Submodule.baseChange_eq_span O' V]`. Apply `full_span` to reduce the goal to its premises. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Take `⟨c, hc, hcv⟩` from `hfull ((1 : Ok) ⊗ₜ[O] v) (Submodule.tmul_mem_baseChange_of_mem 1 hv)`.

Use `⟨algebraMap Ok O' c, (map_ne_zero_iff _ hinj).2 hc, ?_⟩` and prove the remaining obligations. Establish `: algebraMap Ok O' c • (TensorProduct.mk O O' W 1) v = rho O W Ok O' (c • (1 : Ok) ⊗ₜ[O] v)`. Rewrite using `[rho_smul]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `Submodule.subset_span ⟨_, hcv, rfl⟩`.
-/
theorem isLatIn_up [IsDomain O'] (hinj : Function.Injective (algebraMap Ok O'))
    (T : Submodule Ok (Ok ⊗[O] W)) (V : Submodule O W) (h : IsLatIn T (V.baseChange Ok)) :
    IsLatIn (up O' T) (V.baseChange O') := by
  obtain ⟨⟨t, ht⟩, hle, hfull⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← ht, up_span]
    exact Submodule.fg_span (t.finite_toSet.image _)
  · rw [← up_baseChange (Ok := Ok) (O' := O') V]
    exact up_mono hle
  · rw [Submodule.baseChange_eq_span O' V]
    apply full_span
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨c, hc, hcv⟩ := hfull ((1 : Ok) ⊗ₜ[O] v) (Submodule.tmul_mem_baseChange_of_mem 1 hv)
    refine ⟨algebraMap Ok O' c, (map_ne_zero_iff _ hinj).2 hc, ?_⟩
    have : algebraMap Ok O' c • (TensorProduct.mk O O' W 1) v = rho O W Ok O' (c • (1 : Ok) ⊗ₜ[O] v) := by
      rw [rho_smul]; simp
    rw [this]
    exact Submodule.subset_span ⟨_, hcv, rfl⟩

end BC

section Tw

open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt PsiOk)

/- English proof (translation)
Apply the tactic sequence `cases b <;> rfl`.
-/
theorem psiAt_comp {Γ Γ' A : Type} [Group Γ] [Group Γ'] [CommGroup A] (b : Bool) (χ : Γ' →* A)
    (f : Γ →* Γ') : psiAt b (χ.comp f) = (psiAt b χ).comp f := by
  cases b <;> rfl

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7⟩` from `h`. Establish `hk : (ψ⁻¹).ker = ψ.ker`. Use extensionality with `g`. Simplify using `[MonoidHom.mem_ker]`. Use `⟨h1, h2, by rw [hk]; exact h3, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g g' hg`. Simplify using `only [MonoidHom.inv_apply]`. Rewrite using `[h4 g g' hg]`. Introduce `g`. Rewrite using `[MonoidHom.inv_apply]`.

Conclude with `Subgroup.inv_mem _ (h5 g)`. Introduce `v A hA`. Rewrite using `[← h6 v A hA]`. Simplify using the standard rewrite rules. Introduce `v hv A' hA' σ hσ`.

Rewrite using `[MonoidHom.inv_apply, h7 v hv A' hA' σ hσ, inv_one]`.
-/
theorem TwOK_inv {i : X.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ}
    (h : TwOK i k Q ψ) : TwOK i k Q ψ⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hk : (ψ⁻¹).ker = ψ.ker := by
    ext g
    simp [MonoidHom.mem_ker]
  refine ⟨h1, h2, by rw [hk]; exact h3, ?_, ?_, ?_, ?_⟩
  · intro g g' hg
    simp only [MonoidHom.inv_apply]
    rw [h4 g g' hg]
  · intro g
    rw [MonoidHom.inv_apply]
    exact Subgroup.inv_mem _ (h5 g)
  · intro v A hA
    rw [← h6 v A hA]
    simp
  · intro v hv A' hA' σ hσ
    rw [MonoidHom.inv_apply, h7 v hv A' hA' σ hσ, inv_one]

/- English proof (translation)
Consider the cases of `b`. Conclude with `TwOK_inv h`. Conclude with `h`.
-/
theorem TwOK_psiAt {i : X.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ}
    (b : Bool) (h : TwOK i k Q ψ) : TwOK i k Q (psiAt b ψ) := by
  cases b
  · exact TwOK_inv h
  · exact h

/- English proof (translation)
Take `⟨h1, h2, _, h4, h5, h6, h7, h8⟩` from `h`. Conclude with `⟨fun P hP => (h1 P hP).1, (Finset.disjoint_union_right.1 h2).1, h4, h5, h6, h7, h8⟩`.
-/
theorem TwOK_of_PsiOk {i : X.Tw} {A Q : Finset (PlE D.host)} {k' : ℕ} {ψ' : X.RCG i Q →* (X.Ok i k')ˣ}
    (h : PsiOk i A Q k' ψ') : TwOK i k' Q (ψ'.comp (X.art i Q)) := by
  classical
  obtain ⟨h1, h2, _, h4, h5, h6, h7, h8⟩ := h
  exact ⟨fun P hP => (h1 P hP).1, (Finset.disjoint_union_right.1 h2).1, h4, h5, h6, h7, h8⟩

/- English proof (translation)
Introduce `k' v hv A' hA' σ hσ`. Assume the negation of the conclusion as `hne`. Establish `hvQ : v ∈ Q` using `(h.2.2.2.2.2.1 v A' hA').1 ⟨σ, hσ, hne⟩`. Conclude with `Finset.disjoint_left.1 h.2.1 hvQ (X.placesOver_subset_exceptional i k' hv)`.
-/
theorem UnrG_of_TwOK {i : X.Tw} {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ}
    (h : TwOK i k Q ψ) : UnrG ψ := by
  intro k' v hv A' hA' σ hσ
  by_contra hne
  have hvQ : v ∈ Q := (h.2.2.2.2.2.1 v A' hA').1 ⟨σ, hσ, hne⟩
  exact Finset.disjoint_left.1 h.2.1 hvQ (X.placesOver_subset_exceptional i k' hv)

end Tw

/- English proof (translation)
Establish `hinj` using `X.Ok_inj i k`. Establish `: Module.Finite (X.O i) (X.Ok i k)` using `X.Ok_fin i k`. Establish `h0 : ((X.l i : ℕ) : X.O i) ≠ 0`. Introduce `h`. Apply `(Nat.cast_ne_zero (R := FractionRing (X.O i))).2 (X.lPrime i).out.ne_zero` to reduce the goal to its premises.

Rewrite using `[← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), h, map_zero]`. Establish `hne : ((X.l i : ℕ) : X.Ok i k) ≠ 0`. Rewrite using `[← map_natCast (algebraMap (X.O i) (X.Ok i k))]`. Conclude with `(map_ne_zero_iff _ hinj).2 h0`. Establish `hnu : ¬ IsUnit ((X.l i : ℕ) : X.Ok i k)`.

Establish `: FaithfulSMul (X.O i) (X.Ok i k)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Establish `hl : IsLocalHom (algebraMap (X.O i) (X.Ok i k))` using `inferInstance`. Introduce `hu`. Rewrite `hu` using `[← map_natCast (algebraMap (X.O i) (X.Ok i k))]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 (X.O_l i) (hl.map_nonunit _ hu)`.

Establish `h1 : IsDiscreteValuationRing.addVal (X.Ok i k) ((X.l i : ℕ) : X.Ok i k) ≠ 0` using `fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)`. Establish `h2 : IsDiscreteValuationRing.addVal (X.Ok i k) ((X.l i : ℕ) : X.Ok i k) ≠ ⊤` using `fun h => hne (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.1 h2`. Rewrite `h1`, the goal using `[← hn]`. Rewrite using `[ENat.toNat_natCast]`.

Conclude with `Nat.pos_of_ne_zero (by exact_mod_cast h1)`.
-/
theorem addVal_l_pos (i : X.Tw) (k : ℕ) [CharZero (FractionRing (X.O i))] :
    0 < (IsDiscreteValuationRing.addVal (X.Ok i k) ((X.l i : ℕ) : X.Ok i k)).toNat := by
  have hinj := X.Ok_inj i k
  have : Module.Finite (X.O i) (X.Ok i k) := X.Ok_fin i k
  have h0 : ((X.l i : ℕ) : X.O i) ≠ 0 := by
    intro h
    apply (Nat.cast_ne_zero (R := FractionRing (X.O i))).2 (X.lPrime i).out.ne_zero
    rw [← map_natCast (algebraMap (X.O i) (FractionRing (X.O i))), h, map_zero]
  have hne : ((X.l i : ℕ) : X.Ok i k) ≠ 0 := by
    rw [← map_natCast (algebraMap (X.O i) (X.Ok i k))]
    exact (map_ne_zero_iff _ hinj).2 h0
  have hnu : ¬ IsUnit ((X.l i : ℕ) : X.Ok i k) := by
    have : FaithfulSMul (X.O i) (X.Ok i k) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
    have hl : IsLocalHom (algebraMap (X.O i) (X.Ok i k)) := inferInstance
    intro hu
    rw [← map_natCast (algebraMap (X.O i) (X.Ok i k))] at hu
    exact (IsLocalRing.mem_maximalIdeal _).1 (X.O_l i) (hl.map_nonunit _ hu)
  have h1 : IsDiscreteValuationRing.addVal (X.Ok i k) ((X.l i : ℕ) : X.Ok i k) ≠ 0 :=
    fun h => hnu (IsDiscreteValuationRing.addVal_eq_zero_iff.1 h)
  have h2 : IsDiscreteValuationRing.addVal (X.Ok i k) ((X.l i : ℕ) : X.Ok i k) ≠ ⊤ :=
    fun h => hne (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h2
  rw [← hn] at h1 ⊢
  rw [ENat.toNat_natCast]
  exact Nat.pos_of_ne_zero (by exact_mod_cast h1)

/- English proof (translation)
Unfold `Th`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `(mem_typeSubspace_iff_unipotent_character Y _).2 (E.theta_base_equivariant i j b a (hSg ha))`.
-/
theorem theta_le_integral_forms (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b))
    (hSg : Sg ⊆ E.Dat0 i j b) : Th Y i j b Sg ≤ (Fm0 Y i j b).restrictScalars (X.O i) := by
  unfold Th
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  exact (mem_typeSubspace_iff_unipotent_character Y _).2 (E.theta_base_equivariant i j b a (hSg ha))

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, rfl⟩`.
-/
theorem idempotent_image_le_invariants (i : X.Tw) (j : ℕ) (b : Bool) :
    ((Fm0 Y i j b).restrictScalars (X.O i)).map (eO Y i j b) ≤ (V0 Y i j b).restrictScalars (X.O i) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

/- English proof (translation)
The claim follows from `(Submodule.map_mono (theta_le_integral_forms Y E i j b Sg hSg)).trans (idempotent_image_le_invariants Y i j b)`.
-/
theorem eTh_le (E : ExpDat Y) (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b))
    (hSg : Sg ⊆ E.Dat0 i j b) : eTh Y i j b Sg ≤ (V0 Y i j b).restrictScalars (X.O i) :=
  (Submodule.map_mono (theta_le_integral_forms Y E i j b Sg hSg)).trans (idempotent_image_le_invariants Y i j b)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.biUnion_subset_biUnion_left h)`.
-/
theorem ThPsi_mono (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) {Sg Sg' : Set (Y.Dat i j b)} (h : Sg ⊆ Sg') :
    ThPsi Y i j b k Q ψ Sg ≤ ThPsi Y i j b k Q ψ Sg' :=
  Submodule.span_mono (Set.biUnion_subset_biUnion_left h)

/- English proof (translation)
Unfold `ThPsi`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Simplify using `only [Set.mem_iUnion] at hx`. Take `⟨a, ha, hxa⟩` from `hx`.

Conclude with `(hInt i hi j hj b).2.2.2.2.2 k Q ψ hTw (UnrG_of_TwOK hTw) a (hSg ha) hxa`.
-/
theorem ThPsi_le (E : ExpDat Y) (hInt : IsotypicPartsInternalDirectSum Y E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (hTw : TwOK i k Q ψ) (Sg : Set (Y.Dat i j b)) (hSg : Sg ⊆ E.Dat0 i j b) :
    ThPsi Y i j b k Q ψ Sg ≤ ((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) := by
  unfold ThPsi
  rw [Submodule.span_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  exact (hInt i hi j hj b).2.2.2.2.2 k Q ψ hTw (UnrG_of_TwOK hTw) a (hSg ha) hxa

/- English proof (translation)
The claim follows from `(Submodule.map_mono (ThPsi_le Y E hInt i hi j hj b k Q ψ hTw Sg hSg)).trans (map_baseChange_le (X.Ok i k) (eO Y i j b) (idempotent_image_le_invariants Y i j b))`.
-/
theorem eThPsi_le (E : ExpDat Y) (hInt : IsotypicPartsInternalDirectSum Y E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (hTw : TwOK i k Q ψ) (Sg : Set (Y.Dat i j b)) (hSg : Sg ⊆ E.Dat0 i j b) :
    eThPsi Y i j b k Q ψ Sg ≤ ((V0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) :=
  (Submodule.map_mono (ThPsi_le Y E hInt i hi j hj b k Q ψ hTw Sg hSg)).trans
    (map_baseChange_le (X.Ok i k) (eO Y i j b) (idempotent_image_le_invariants Y i j b))

/- English proof (translation)
Establish `hle` using `hT4 i hi j hj b k Q ψ hTw Sg hSg`. Establish `hfg : ((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ)).FG` using `(Y.MtLat_fg i j b k Q ψ).map _`. Establish `: IsNoetherian (X.Ok i k) ↥((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ))` using `isNoetherian_of_fg_of_noetherian _ hfg`. Conclude with `(isNoetherian_submodule.1 this) _ hle`.
-/
theorem ThPsi_fg (E : ExpDat Y) (hT4 : admT4 Y E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (hTw : TwOK i k Q ψ) (Sg : Set (Y.Dat i j b)) (hSg : Sg ⊆ E.Dat0 i j b) :
    (ThPsi Y i j b k Q ψ Sg).FG := by
  have hle := hT4 i hi j hj b k Q ψ hTw Sg hSg
  have hfg : ((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ)).FG := (Y.MtLat_fg i j b k Q ψ).map _
  have : IsNoetherian (X.Ok i k) ↥((Y.MtLat i j b k Q ψ).map (Y.thP i j b k Q ψ)) :=
    isNoetherian_of_fg_of_noetherian _ hfg
  exact (isNoetherian_submodule.1 this) _ hle

/- English proof (translation)
The claim follows from `Submodule.map_mono (hT4 i hi j hj b k Q ψ hTw Sg hSg)`.
-/
theorem InclAt_of (E : ExpDat Y) (hT4 : admT4 Y E) (i : X.Tw) (hi : X.NonzeroIndexPlace i) (j : ℕ) (hj : j ∈ Finset.Icc 1 D.R.m)
    (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (hTw : TwOK i k Q ψ) (Sg : Set (Y.Dat i j b)) (hSg : Sg ⊆ E.Dat0 i j b) :
    InclAt Y i j b Sg k Q ψ :=
  Submodule.map_mono (hT4 i hi j hj b k Q ψ hTw Sg hSg)

/- English proof (translation)
The claim follows from `map_smul_eq_scaleLat _ _ _`.
-/
theorem map_AO_eq (i : X.Tw) (j : ℕ) (b : Bool) (Sg : Set (Y.Dat i j b)) :
    (Th Y i j b Sg).map (AO Y i j b) =
      Formalism.IrreducibleCountingLemmas.TW.scaleLat ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.O i) (eTh Y i j b Sg) :=
  map_smul_eq_scaleLat _ _ _

/- English proof (translation)
Unfold `AO`. Rewrite using `[LinearMap.baseChange_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`.
-/
theorem AO_baseChange (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) :
    (AO Y i j b).baseChange (X.Ok i k) =
      ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.Ok i k) • (eO Y i j b).baseChange (X.Ok i k) := by
  unfold AO
  rw [LinearMap.baseChange_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Rewrite using `[AO_baseChange]`. Conclude with `map_smul_eq_scaleLat _ _ _`.
-/
theorem map_AO_baseChange_eq (i : X.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) (Sg : Set (Y.Dat i j b)) :
    (ThPsi Y i j b k Q ψ Sg).map ((AO Y i j b).baseChange (X.Ok i k)) =
      Formalism.IrreducibleCountingLemmas.TW.scaleLat ((D.what₂.restRowsFiniteGroupCard : ℕ) : X.Ok i k) (eThPsi Y i j b k Q ψ Sg) := by
  rw [AO_baseChange]
  exact map_smul_eq_scaleLat _ _ _

instance charZero_K (D : Formalism.BasicNotions.D7) (i : D.ntw.Tw) : CharZero (FractionRing (D.ntw.O i)) :=
  (D.nth.iC i).charZero

/- English proof (translation)
The claim follows from `eAlg_integral D.nexp i b`.
-/
theorem idempotent_scaled_integral (D : Formalism.BasicNotions.D7) (i : D.ntw.Tw) (b : Bool) :
    ∃ c : MonoidAlgebra (D.ntw.O i) (G0g D.nd),
      MonoidAlgebra.map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (D.ntw.O i)) • D.nexp.eAlg i b :=
  eAlg_integral D.nexp i b

/- English proof (translation)
The claim follows from `eG_irred D.nexp i j b W hW`.
-/
theorem idempotent_irreducible_dichotomy (D : Formalism.BasicNotions.D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool)
    (W : Submodule (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (hW : GIrred D.nexp i j b W) :
    (∀ x ∈ W, eG D.nexp i j b x = x) ∨ (∀ x ∈ W, eG D.nexp i j b x = 0) :=
  eG_irred D.nexp i j b W hW

def HeckeCommutation (D : Formalism.BasicNotions.D7) : Prop := HeckeCommutesLevelGroup D.nexp

/- English proof (translation)
The claim follows from `admissibleGoodIdempotent_iff_reduced D.nexp`.
-/
theorem algebraicity_iff_commutation (D : Formalism.BasicNotions.D7) : adm5 D ↔ HeckeCommutation D := admissibleGoodIdempotent_iff_reduced D.nexp

/- English proof (translation)
The claim follows from `(algebraicity_iff_commutation D).2 h`.
-/
theorem algebraicity_of_commutation (D : Formalism.BasicNotions.D7) (h : HeckeCommutation D) : adm5 D := (algebraicity_iff_commutation D).2 h

/- English proof (translation)
Establish `: IsNoetherian (D.ntw.O i) ↥(D.nexp.Bsup i j b)` using `isNoetherian_of_fg_of_noetherian _ (Formalism.MainNotions.ExistsIdealDenominator.Bsup_fg D i j b)`. Conclude with `(isNoetherian_submodule.1 this) _ inf_le_left`.
-/
theorem sup_lattice_finitely_generated (D : Formalism.BasicNotions.D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : (Mall D.nexp i j b).FG := by
  have : IsNoetherian (D.ntw.O i) ↥(D.nexp.Bsup i j b) :=
    isNoetherian_of_fg_of_noetherian _ (Formalism.MainNotions.ExistsIdealDenominator.Bsup_fg D i j b)
  exact (isNoetherian_submodule.1 this) _ inf_le_left

/- English proof (translation)
Introduce and unpack `_ ⟨x, ⟨hx1, hx2⟩, rfl⟩`. Take `⟨hj1, hj2⟩` from `Finset.mem_Icc.1 hj`. Conclude with `⟨hB i j b k P hj1 hj2 h.1 h.2.1 h.2.2.1 h.2.2.2 x hx1, commuting_endomorphism_preserves_forms D.nexp i j b _ (fun g => hC i hi b j hj g k P h) hx2⟩`.
-/
theorem hecke_preserves_sup_lattice (D : Formalism.BasicNotions.D7) (hB : Formalism.MainNotions.ExistsIdealDenominator.IntegralitySecondClauseSupLattice D) (hC : HeckeCommutation D) (i : D.ntw.Tw) (hi : D.ntw.NonzeroIndexPlace i) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) (k : ℕ) (P : PlE D.host) (h : HkIdx i k P) :
    (Mall D.nexp i j b).map (hkO D.nexp i j b k P) ≤ Mall D.nexp i j b := by
  rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  exact ⟨hB i j b k P hj1 hj2 h.1 h.2.1 h.2.2.1 h.2.2.2 x hx1,
    commuting_endomorphism_preserves_forms D.nexp i j b _ (fun g => hC i hi b j hj g k P h) hx2⟩

def IntegralityRemainder (D : Formalism.BasicNotions.D7) (E : XD D) : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool),
    (∀ g, (D.nexp.Bsup i j b).map ((D.nexp.actG i j b g).toLinearMap.restrictScalars (D.ntw.O i)) ≤
      D.nexp.Bsup i j b) ∧
    Submodule.span (FractionRing (D.ntw.O i)) (Mall D.nexp i j b : Set (D.nexp.Fm i j b)) =
      Fm0 D.nexp i j b ∧
    (∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M, (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q →
      Disjoint Q (D.ntw.S0 i) → Disjoint Q (D.nexp.lev i j b a) →
      ((D.ntw.l i : D.ntw.O i) ^ c) • D.nexp.thU i j b Q M a ∈
        LinearMap.range ((Mall D.nexp i j b).subtype.rTensor _)) ∧
    (∀ k Q (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ →
      ∀ a ∈ E.Dat0 i j b,
      D.nexp.thPsi i j b k Q ψ a ⊆
        ((((Fm0 D.nexp i j b).restrictScalars (D.ntw.O i)).baseChange (D.ntw.Ok i k) :
          Submodule (D.ntw.Ok i k) (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)) :
            Set (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)))

/- English proof (translation)
Introduce `i hi j hj b`. Take `⟨h1, h3, h5, h6⟩` from `h i hi j hj b`. Conclude with `⟨h1, sup_lattice_finitely_generated D i j b, h3, fun k P hk => hecke_preserves_sup_lattice D hB hC i hi j hj b k P hk, h5, h6⟩`.
-/
theorem integrality_of_commutation (D : Formalism.BasicNotions.D7) (E : XD D) (h : IntegralityRemainder D E) (hB : Formalism.MainNotions.ExistsIdealDenominator.IntegralitySecondClauseSupLattice D) (hC : HeckeCommutation D) :
    adm3 D E := by
  intro i hi j hj b
  obtain ⟨h1, h3, h5, h6⟩ := h i hi j hj b
  exact ⟨h1, sup_lattice_finitely_generated D i j b, h3, fun k P hk => hecke_preserves_sup_lattice D hB hC i hi j hj b k P hk, h5, h6⟩

/- English proof (translation)
Introduce `i hi j hj b`. Take `⟨h1, _, h3, _, h5, h6⟩` from `h i hi j hj b`. Conclude with `⟨h1, h3, h5, h6⟩`.
-/
theorem integrality_clause_of_full (D : Formalism.BasicNotions.D7) (E : XD D) (h : adm3 D E) : IntegralityRemainder D E := by
  intro i hi j hj b
  obtain ⟨h1, _, h3, _, h5, h6⟩ := h i hi j hj b
  exact ⟨h1, h3, h5, h6⟩

end Formalism.MainNotions.IntegralHeckeForms

end
