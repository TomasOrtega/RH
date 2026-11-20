import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAct
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverPoly
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverVal

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain Module Module.End Polynomial

namespace Formalism.L2.NCov

def intPrimeTo (R : Type*) [CommRing R] {l : ℕ} (hl : l.Prime) : Subring R where
  carrier := {a | ∃ d : ℕ, ¬ l ∣ d ∧ IsIntegral ℤ ((d : R) * a)}
  one_mem' := ⟨1, fun h => hl.one_lt.ne' (Nat.dvd_one.1 h), by simpa using isIntegral_one⟩
  mul_mem' := by
    rintro a b ⟨d₁, hd₁, h₁⟩ ⟨d₂, hd₂, h₂⟩
    refine ⟨d₁ * d₂, fun h => (hl.dvd_mul.1 h).elim hd₁ hd₂, ?_⟩
    have e : ((d₁ * d₂ : ℕ) : R) * (a * b) = ((d₁ : R) * a) * ((d₂ : R) * b) := by push_cast; ring
    rw [e]; exact h₁.mul h₂
  zero_mem' := ⟨1, fun h => hl.one_lt.ne' (Nat.dvd_one.1 h), by simpa using isIntegral_zero⟩
  add_mem' := by
    rintro a b ⟨d₁, hd₁, h₁⟩ ⟨d₂, hd₂, h₂⟩
    refine ⟨d₁ * d₂, fun h => (hl.dvd_mul.1 h).elim hd₁ hd₂, ?_⟩
    have e : ((d₁ * d₂ : ℕ) : R) * (a + b) = (d₂ : R) * ((d₁ : R) * a) + (d₁ : R) * ((d₂ : R) * b) := by
      push_cast; ring
    have hn : ∀ m : ℕ, IsIntegral ℤ (m : R) := fun m => by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := R) (x := (m : ℤ)))
    rw [e]
    exact ((hn d₂).mul h₁).add ((hn d₁).mul h₂)
  neg_mem' := by
    rintro a ⟨d, hd, h⟩
    refine ⟨d, hd, ?_⟩
    rw [mul_neg]; exact h.neg

/- English proof (translation)
Establish `hmem : (s.map fun μ => X - C μ).prod ∈ Polynomial.liftsRing S.subtype`. Apply `Subring.multiset_prod_mem` to reduce the goal to its premises. Introduce `p hp`. Take `⟨μ, hμ, rfl⟩` from `Multiset.mem_map.mp hp`. Conclude with `⟨X - C ⟨μ, hs μ hμ⟩, by simp⟩`.

Rewrite `hmem` using `[← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts]`. Take `⟨c, hc⟩` from `hmem n`. Rewrite using `[← hc]`. Conclude with `c.2`.
-/
theorem coeff_prod_mem {R : Type*} [CommRing R] (S : Subring R) (s : Multiset R) (hs : ∀ μ ∈ s, μ ∈ S) (n : ℕ) :
    ((s.map fun μ => X - C μ).prod).coeff n ∈ S := by
  have hmem : (s.map fun μ => X - C μ).prod ∈ Polynomial.liftsRing S.subtype := by
    apply Subring.multiset_prod_mem
    intro p hp
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hp
    exact ⟨X - C ⟨μ, hs μ hμ⟩, by simp⟩
  rw [← Polynomial.lifts_iff_liftsRing, Polynomial.lifts_iff_coeff_lifts] at hmem
  obtain ⟨c, hc⟩ := hmem n
  rw [← hc]
  exact c.2

/- English proof (translation)
Proceed by induction on `d using Nat.recOnMul with`. Consider the case `zero => exact absurd (dvd_zero l) hd`. Consider the case `one => simp`. Consider the case `prime p hp => exact val_prime_eq_zero v hl hp (fun h => hd (h ▸ dvd_refl l)) hvl`. Consider the case `mul a b ha hb`.

Establish `ha'` using `ha fun h => hd (h.mul_right b)`. Establish `hb'` using `hb fun h => hd (h.mul_left a)`. Rewrite using `[Nat.cast_mul, AddValuation.map_mul, ha', hb', add_zero]`.
-/
theorem val_eq_zero_of_not_dvd {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ)) {l : ℕ} (hl : l.Prime)
    (hvl : 0 < v (l : F)) (d : ℕ) (hd : ¬ l ∣ d) : v (d : F) = 0 := by
  induction d using Nat.recOnMul with
  | zero => exact absurd (dvd_zero l) hd
  | one => simp
  | prime p hp => exact val_prime_eq_zero v hl hp (fun h => hd (h ▸ dvd_refl l)) hvl
  | mul a b ha hb =>
    have ha' := ha fun h => hd (h.mul_right b)
    have hb' := hb fun h => hd (h.mul_left a)
    rw [Nat.cast_mul, AddValuation.map_mul, ha', hb', add_zero]

end Formalism.L2.NCov

namespace Formalism.L2

variable {D : D7} {M : MtFam D}

def GenOutBad (T : NormalizedLocalCompatibility D M) : Prop :=
  ∀ j w i (h : i ∈ D.nd.locs j w) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E),
    GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k → IsConjPl D.host v s.w → s.v ∉ badPl D i

/- English proof (translation)
Substitute `hμ hj` using the available equality. Conclude with `id`.
-/
theorem hypOutside_transport {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ = μ') (hj : j = j')
    (a1 : 1 ≤ j) (a2 : j ≤ D.R.m) (b1 : 1 ≤ j') (b2 : j' ≤ D.R.m)
    (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) :
    NG.HypOutside (M μ j a1 a2).J (M μ j a1 a2).χ B → NG.HypOutside (M μ' j' b1 b2).J (M μ' j' b1 b2).χ B := by
  subst hμ hj
  exact id

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)`. Establish `hb` using `(D.what₂.jMt_basis μ j b).1`. Establish `: Finite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))` using `hb.finite`. Use `haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))`. Use `(injective_iff_map_eq_zero (D.what₂.jMt μ j)).2 fun y hy => ?_` and prove the remaining obligations.

Establish `hsum` using `b.sum_repr y`. Rewrite `hy` using `[← hsum, map_sum]`. Simplify using `only [LinearMap.map_smulₛₗ] at hy`. Establish `hz` using `Fintype.linearIndependent_iff.1 hb _ hy`. Rewrite using `[← hsum]`.

Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[(map_eq_zero_iff _ D.what₂.embLL.injective).1 (hz a), zero_smul]`.
-/
theorem jMt_injective (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  classical
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)
  have hb := (D.what₂.jMt_basis μ j b).1
  have : Finite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j)) := hb.finite
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  refine (injective_iff_map_eq_zero (D.what₂.jMt μ j)).2 fun y hy => ?_
  have hsum := b.sum_repr y
  rw [← hsum, map_sum] at hy
  simp only [LinearMap.map_smulₛₗ] at hy
  have hz := Fintype.linearIndependent_iff.1 hb _ hy
  rw [← hsum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [(map_eq_zero_iff _ D.what₂.embLL.injective).1 (hz a), zero_smul]

/- English proof (translation)
Introduce `hA`. Apply `hvk.2.1` to reduce the goal to its premises. Establish `h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (l : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.w.asIdeal`. Rewrite using `[← Ideal.mem_comap, s.w_under]`. Conclude with `hA`.

Rewrite `h1` using `[map_natCast]`. Conclude with `(hc (l : 𝓞 D.host.E) (l : 𝓞 D.host.E) (by simp)).2 h1`.
-/
theorem not_above {l : ℕ} {Q : Finset (PlE D.host)} {v : PlE D.host} {k : ℕ} (hvk : GenAt D l Q v k)
    (s : SplitPlace D.host.E) (hc : IsConjPl D.host v s.w) : ¬ s.Above l := by
  intro hA
  apply hvk.2.1
  have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (l : 𝓞 (maximalRealSubfield D.host.E)) ∈
      s.w.asIdeal := by
    rw [← Ideal.mem_comap, s.w_under]; exact hA
  rw [map_natCast] at h1
  exact (hc (l : 𝓞 D.host.E) (l : 𝓞 D.host.E) (by simp)).2 h1

/- English proof (translation)
Introduce `j w h1 h2 hw`. Take `⟨hfd, -⟩` from `finrank_V T.B j w`. Use `haveI := hfd`. Distinguish the cases in `hne : (D.nd.locs j w).Nonempty`. Use `swap`.

Establish `hsub : Subsingleton (T.B.V j w)`. Assume the negation of the conclusion as `hnt`. Rewrite `hnt` using `[not_subsingleton_iff_nontrivial]`. Establish `h01 : (0 : Module.End (FractionRing (T.B.Oc j w)) (T.B.V j w)) ≠ 1` using `zero_ne_one`. Use `haveI : Nontrivial (heckeAlg T.B j w) := ⟨⟨0, 1, fun h => h01 (congrArg Subtype.val h)⟩⟩`.

Take `⟨I, hI⟩` from `Ideal.exists_maximal (heckeAlg T.B j w)`. Take `⟨i, hi, -⟩` from `T.mx_all j w h1 h2 (hw.resolve_right hne) I hI`. Conclude with `hne ⟨i, hi⟩`. Use `⟨fun _ _ _ _ _ _ => LinearMap.ext fun _ => Subsingleton.elim _ _, fun _ _ _ μ hμ => ?_⟩` and prove the remaining obligations. Conclude with `absurd (Subsingleton.elim _ _) hμ`.

Take `⟨i0, hi0⟩` from `hne`. Take `⟨e1, e2⟩` from `(D.nd.locs_mem j w i0).1 hi0`. Establish `hμ : D.nd.mu i0 = D.what₂.muTw w` using `by rw [D.nd.mu_w i0, e2]`. Establish `hJ : NG.HypOutside (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ (badPl D i0)` using `hypOutside_transport hμ e1 (D.nd.j_range i0).1 (D.nd.j_range i0).2 h1 h2 _ (HT.J_hyp i0)`. Establish `hRJ : Function.Injective fun x => (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x)` using `(M (D.what₂.muTw w) j h1 h2).real_inj.comp (jMt_injective _ _)`.

Establish `hTS : ∀ y, (M (D.what₂.muTw w) j h1 h2).real y ∈ NG.TypeSp (M (D.what₂.muTw w) j h1 h2).wt.ρ (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ`. Introduce `y`. Rewrite using `[← (M (D.what₂.muTw w) j h1 h2).real_range]`. Conclude with `LinearMap.mem_range_self _ y`. Establish `plain` using `fun (v : PlE D.host) (k : ℕ) (hvk : GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hc : IsConjPl D.host v s.w) (hu : IsUnif D.host.E s.v ϖ) => hP D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2). …`.

Use `haveI := finite_chooseBasisIndex (D := D) j w`. Use `haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))`. Set `b` to `Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)`. Use `haveI : Module.Finite D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := Module.Finite.of_basis b`. Establish `hb` using `T.B.iV_basis j w b`.

Set `bV` to `Module.Basis.mk hb.1 hb.2.ge`. Use `⟨fun v k v' k' hvk hvk' => ?_, fun v k hvk μ hμ0 => ?_⟩` and prove the remaining obligations. Take `⟨s, ϖ, hc, hu⟩` from `hex v hvk.1`. Take `⟨s', ϖ', hc', hu'⟩` from `hex v' hvk'.1`. Take `⟨-, -, Pcomm, -⟩` from `plain v k hvk s ϖ hc hu`.

Establish `hd` using `T.B.hL_def j w h1 h2 v k s ϖ hvk hc hu`. Establish `hd'` using `T.B.hL_def j w h1 h2 v' k' s' ϖ' hvk' hc' hu'`. Establish `hLc : ∀ x, T.B.hL j w v k (T.B.hL j w v' k' x) = T.B.hL j w v' k' (T.B.hL j w v k x)`. Introduce `x`. Apply `hRJ` to reduce the goal to its premises.

Simplify using `only`. Rewrite using `[hd, hd', Pcomm s' ϖ' k' (hbad j w i0 hi0 v' k' s' hvk' hc') hu' hvk'.2.2.2.2.1 hvk'.2.2.2.2.2 _ (hTS _), ← hd, ← hd']`. Use `show T.B.hK j w v k * T.B.hK j w v' k' = T.B.hK j w v' k' * T.B.hK j w v k`. Use `bV.ext fun a => ?_` and prove the remaining obligations. Simplify using `only [bV, Module.Basis.mk_apply, Module.End.mul_apply, T.B.hK_def, hLc]`.

Take `⟨s, ϖ, hc, hu⟩` from `hex v hvk.1`. Take `⟨P0, Plin, -, Pint⟩` from `plain v k hvk s ϖ hc hu`. Use `set Mw := M (D.what₂.muTw w) j h1 h2`. Establish `hd` using `T.B.hL_def j w h1 h2 v k s ϖ hvk hc hu`. Establish `hev : (T.B.hK j w v k).HasEigenvalue μ`.

Rewrite `hμ0` using `[maxGenEigenspace_eq]`. Conclude with `hasEigenvalue_of_hasGenEigenvalue hμ0`. Establish `hroot` using `(hasEigenvalue_iff_isRoot_charpoly _ _).1 hev`. Use `haveI : Module.Finite (FractionRing (T.B.Oc j w)) (T.B.V j w) := hfd`. Establish `hKpoly : (T.B.hK j w v k).charpoly = (T.B.hL j w v k).charpoly.map (T.B.ec j w)` using `NCov.charpoly_transport (T.B.ec j w) (T.B.iV j w) b hb.1 hb.2 _ _ (fun x => T.B.hK_def j w v k x)`.

Establish `hjb` using `D.what₂.jMt_basis (D.what₂.muTw w) j b`. Set `bC` to `Module.Basis.mk hjb.1 hjb.2.ge`. Set `tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j)` to `bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (T.B.hL j w v k (b a))`. Establish `hCpoly : tC.charpoly = (T.B.hL j w v k).charpoly.map D.what₂.embLL` using `NCov.charpoly_transport_basis D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 _ _ fun a => by`. Establish `e` using `bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (T.B.hL j w v k (b a))) a`.

Simplify using `only [bC, Module.Basis.mk_apply] at e`. Conclude with `e`. Establish `htN0 : NG.tN Mw.J s ϖ k (0 : GAf D.host.E D.R.nV → Mw.wt.W) = 0`. Use `Plin (0 : GAf D.host.E D.R.nV → Mw.wt.W) (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1` as an intermediate fact. Rewrite `this` using `[one_smul, add_zero, one_smul]`.

Simplify using `using this`. Set `Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (GAf D.host.E D.R.nV → Mw.wt.W)` to `{ toFun := fun y => NG.tN Mw.J s ϖ k (Mw.real y) map_add' := fun y y' => by`. Use `Plin (Mw.real y) (hTS y) (Mw.real y') (hTS y') 1` as an intermediate fact. Rewrite `this` using `[one_smul, one_smul]`. Simplify using `only [map_add]`.

Conclude with `this`. Use the proof step `map_smul' := fun c y => by`. Use `Plin (Mw.real y) (hTS y) 0 (Submodule.zero_mem _) c` as an intermediate fact. Rewrite `this` using `[add_zero, htN0, add_zero]`. Simplify using `only [map_smul, RingHom.id_apply]`.

Conclude with `this }`. Establish `hagree : ∀ y, NG.tN Mw.J s ϖ k (Mw.real y) = Mw.real (tC y)`. Establish `hLt : Lt = Mw.real.comp tC` using `bC.ext fun a => by`. Establish `e` using `bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (T.B.hL j w v k (b a))) a`. Establish `hba : bC a = D.what₂.jMt (D.what₂.muTw w) j (b a)` using `by simp [bC]`.

Use `show NG.tN Mw.J s ϖ k (Mw.real (bC a)) = Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (T.B.hL j w v k (b a))) (bC a))`. Rewrite using `[e, hba]`. Conclude with `(hd (b a)).symm`. Introduce `y`. Conclude with `LinearMap.congr_fun hLt y`.

Establish `hl` using `D.what₂.places.resChar_prime w`. Establish `hnotA` using `not_above hvk s hc`. Establish `hroots : ∀ μ' ∈ tC.charpoly.roots, μ' ∈ NCov.intPrimeTo ℂ hl`. Introduce `μ' hμ'`. Establish `hr : tC.charpoly.IsRoot μ'` using `(mem_roots (LinearMap.charpoly_monic tC).ne_zero).1 hμ'`.

Take `⟨y, hy⟩` from `((hasEigenvalue_iff_isRoot_charpoly _ _).2 hr).exists_hasEigenvector`. Establish `hy1 : tC y = μ' • y` using `mem_eigenspace_iff.1 hy.1`. Establish `hf0 : Mw.real y ≠ 0` using `fun h0 => hy.2 (Mw.real_inj (h0.trans (map_zero _).symm))`. Establish `heig : NG.tN Mw.J s ϖ k (Mw.real y) = μ' • Mw.real y` using `by rw [hagree, hy1, map_smul]`. Conclude with `Pint _ (hTS y) hf0 μ' heig _ hl hnotA`.

Establish `hvl : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)`. Rewrite using `[D.what₂.places.val_resChar w]`. Conclude with `D.what₂.places.ramIdx_pos w` after adjusting the coercions. Establish `hcoef : ∀ n, T.B.ec j w ((T.B.hL j w v k).charpoly.coeff n) ∈ (algebraMap (T.B.Oc j w) (FractionRing (T.B.Oc j w))).range`. Introduce `n`.

Establish `hprod` using `(IsAlgClosed.splits tC.charpoly).eq_prod_roots_of_monic (LinearMap.charpoly_monic tC)`. Establish `hmem : tC.charpoly.coeff n ∈ NCov.intPrimeTo ℂ hl`. Rewrite using `[hprod]`. Conclude with `NCov.coeff_prod_mem _ _ hroots n`. Rewrite `hmem` using `[hCpoly, coeff_map]`.

Take `⟨d, hd0, hint⟩` from `hmem`. Use `set c := (T.B.hL j w v k).charpoly.coeff n`. Establish `hint' : IsIntegral ℤ ((d : D.what₂.LL) * c)`. Establish `e : (d : ℂ) * D.what₂.embLL c = D.what₂.embLL ((d : D.what₂.LL) * c)` using `by simp`. Rewrite `hint` using `[e]`.

Conclude with `(isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 hint`. Establish `hv1` using `NCov.nonneg_of_isIntegral (D.what₂.places.val w) hint'`. Establish `hvd` using `NCov.val_eq_zero_of_not_dvd (D.what₂.places.val w) hl hvl d hd0`. Rewrite `hv1` using `[AddValuation.map_mul, hvd, zero_add]`. Conclude with `(T.B.ec_w j w c).1 hv1`.

Rewrite `hroot` using `[hKpoly]`. Use `NCov.mem_range_of_isRoot _ ((LinearMap.charpoly_monic _).map _) (fun n => ?_) hroot` and prove the remaining obligations. Rewrite using `[coeff_map]`. Conclude with `hcoef n`.
-/
theorem heckeStd_of_plain (T : NormalizedLocalCompatibility D M) (hP : HeckeStdPlain) (HT : HeckeTied D M) (hex : SplitEx D)
    (hbad : GenOutBad T) : HeckeStdTw T.B := by
  intro j w h1 h2 hw
  classical
  obtain ⟨hfd, -⟩ := finrank_V T.B j w
  haveI := hfd
  by_cases hne : (D.nd.locs j w).Nonempty
  swap
  · have hsub : Subsingleton (T.B.V j w) := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      have h01 : (0 : Module.End (FractionRing (T.B.Oc j w)) (T.B.V j w)) ≠ 1 := zero_ne_one
      haveI : Nontrivial (heckeAlg T.B j w) := ⟨⟨0, 1, fun h => h01 (congrArg Subtype.val h)⟩⟩
      obtain ⟨I, hI⟩ := Ideal.exists_maximal (heckeAlg T.B j w)
      obtain ⟨i, hi, -⟩ := T.mx_all j w h1 h2 (hw.resolve_right hne) I hI
      exact hne ⟨i, hi⟩
    refine ⟨fun _ _ _ _ _ _ => LinearMap.ext fun _ => Subsingleton.elim _ _, fun _ _ _ μ hμ => ?_⟩
    exact absurd (Subsingleton.elim _ _) hμ
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨e1, e2⟩ := (D.nd.locs_mem j w i0).1 hi0
  have hμ : D.nd.mu i0 = D.what₂.muTw w := by rw [D.nd.mu_w i0, e2]
  have hJ : NG.HypOutside (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ (badPl D i0) :=
    hypOutside_transport hμ e1 (D.nd.j_range i0).1 (D.nd.j_range i0).2 h1 h2 _ (HT.J_hyp i0)
  have hRJ : Function.Injective fun x => (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x) :=
    (M (D.what₂.muTw w) j h1 h2).real_inj.comp (jMt_injective _ _)
  have hTS : ∀ y, (M (D.what₂.muTw w) j h1 h2).real y ∈
      NG.TypeSp (M (D.what₂.muTw w) j h1 h2).wt.ρ (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ := by
    intro y
    rw [← (M (D.what₂.muTw w) j h1 h2).real_range]
    exact LinearMap.mem_range_self _ y
  have plain := fun (v : PlE D.host) (k : ℕ) (hvk : GenAt D (D.what₂.places.resChar w) (T.B.Qc j w) v k)
      (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
      (hc : IsConjPl D.host v s.w) (hu : IsUnif D.host.E s.v ϖ) =>
    hP D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
      (M (D.what₂.muTw w) j h1 h2).χ (badPl D i0) (M (D.what₂.muTw w) j h1 h2).J_open hJ s ϖ k
      (hbad j w i0 hi0 v k s hvk hc) hu hvk.2.2.2.2.1 hvk.2.2.2.2.2
  haveI := finite_chooseBasisIndex (D := D) j w
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)
  haveI : Module.Finite D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := Module.Finite.of_basis b
  have hb := T.B.iV_basis j w b
  let bV := Module.Basis.mk hb.1 hb.2.ge
  refine ⟨fun v k v' k' hvk hvk' => ?_, fun v k hvk μ hμ0 => ?_⟩
  · obtain ⟨s, ϖ, hc, hu⟩ := hex v hvk.1
    obtain ⟨s', ϖ', hc', hu'⟩ := hex v' hvk'.1
    obtain ⟨-, -, Pcomm, -⟩ := plain v k hvk s ϖ hc hu
    have hd := T.B.hL_def j w h1 h2 v k s ϖ hvk hc hu
    have hd' := T.B.hL_def j w h1 h2 v' k' s' ϖ' hvk' hc' hu'
    have hLc : ∀ x, T.B.hL j w v k (T.B.hL j w v' k' x) = T.B.hL j w v' k' (T.B.hL j w v k x) := by
      intro x
      apply hRJ
      simp only
      rw [hd, hd', Pcomm s' ϖ' k' (hbad j w i0 hi0 v' k' s' hvk' hc') hu' hvk'.2.2.2.2.1 hvk'.2.2.2.2.2 _ (hTS _),
        ← hd, ← hd']
    show T.B.hK j w v k * T.B.hK j w v' k' = T.B.hK j w v' k' * T.B.hK j w v k
    refine bV.ext fun a => ?_
    simp only [bV, Module.Basis.mk_apply, Module.End.mul_apply, T.B.hK_def, hLc]
  · obtain ⟨s, ϖ, hc, hu⟩ := hex v hvk.1
    obtain ⟨P0, Plin, -, Pint⟩ := plain v k hvk s ϖ hc hu
    set Mw := M (D.what₂.muTw w) j h1 h2
    have hd := T.B.hL_def j w h1 h2 v k s ϖ hvk hc hu

    have hev : (T.B.hK j w v k).HasEigenvalue μ := by
      rw [maxGenEigenspace_eq] at hμ0
      exact hasEigenvalue_of_hasGenEigenvalue hμ0
    have hroot := (hasEigenvalue_iff_isRoot_charpoly _ _).1 hev
    haveI : Module.Finite (FractionRing (T.B.Oc j w)) (T.B.V j w) := hfd
    have hKpoly : (T.B.hK j w v k).charpoly = (T.B.hL j w v k).charpoly.map (T.B.ec j w) :=
      NCov.charpoly_transport (T.B.ec j w) (T.B.iV j w) b hb.1 hb.2 _ _ (fun x => T.B.hK_def j w v k x)

    have hjb := D.what₂.jMt_basis (D.what₂.muTw w) j b
    let bC := Module.Basis.mk hjb.1 hjb.2.ge
    let tC : Module.End ℂ (D.what₂.Mt (D.what₂.muTw w) j) :=
      bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (T.B.hL j w v k (b a))
    have hCpoly : tC.charpoly = (T.B.hL j w v k).charpoly.map D.what₂.embLL :=
      NCov.charpoly_transport_basis D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j) b hjb.1 hjb.2 _ _ fun a => by
        have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (T.B.hL j w v k (b a))) a
        simp only [bC, Module.Basis.mk_apply] at e
        exact e
    have htN0 : NG.tN Mw.J s ϖ k (0 : GAf D.host.E D.R.nV → Mw.wt.W) = 0 := by
      have := Plin (0 : GAf D.host.E D.R.nV → Mw.wt.W) (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
      rw [one_smul, add_zero, one_smul] at this
      simpa using this
    let Lt : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (GAf D.host.E D.R.nV → Mw.wt.W) :=
      { toFun := fun y => NG.tN Mw.J s ϖ k (Mw.real y)
        map_add' := fun y y' => by
          have := Plin (Mw.real y) (hTS y) (Mw.real y') (hTS y') 1
          rw [one_smul, one_smul] at this
          simp only [map_add]
          exact this
        map_smul' := fun c y => by
          have := Plin (Mw.real y) (hTS y) 0 (Submodule.zero_mem _) c
          rw [add_zero, htN0, add_zero] at this
          simp only [map_smul, RingHom.id_apply]
          exact this }
    have hagree : ∀ y, NG.tN Mw.J s ϖ k (Mw.real y) = Mw.real (tC y) := by
      have hLt : Lt = Mw.real.comp tC := bC.ext fun a => by
        have e := bC.constr_basis ℂ (fun a => D.what₂.jMt (D.what₂.muTw w) j (T.B.hL j w v k (b a))) a
        have hba : bC a = D.what₂.jMt (D.what₂.muTw w) j (b a) := by simp [bC]
        show NG.tN Mw.J s ϖ k (Mw.real (bC a)) =
          Mw.real ((bC.constr ℂ fun a => D.what₂.jMt (D.what₂.muTw w) j (T.B.hL j w v k (b a))) (bC a))
        rw [e, hba]
        exact (hd (b a)).symm
      intro y
      exact LinearMap.congr_fun hLt y
    have hl := D.what₂.places.resChar_prime w
    have hnotA := not_above hvk s hc
    have hroots : ∀ μ' ∈ tC.charpoly.roots, μ' ∈ NCov.intPrimeTo ℂ hl := by
      intro μ' hμ'
      have hr : tC.charpoly.IsRoot μ' := (mem_roots (LinearMap.charpoly_monic tC).ne_zero).1 hμ'
      obtain ⟨y, hy⟩ := ((hasEigenvalue_iff_isRoot_charpoly _ _).2 hr).exists_hasEigenvector
      have hy1 : tC y = μ' • y := mem_eigenspace_iff.1 hy.1
      have hf0 : Mw.real y ≠ 0 := fun h0 => hy.2 (Mw.real_inj (h0.trans (map_zero _).symm))
      have heig : NG.tN Mw.J s ϖ k (Mw.real y) = μ' • Mw.real y := by rw [hagree, hy1, map_smul]
      exact Pint _ (hTS y) hf0 μ' heig _ hl hnotA
    have hvl : 0 < D.what₂.places.val w ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
      rw [D.what₂.places.val_resChar w]
      exact_mod_cast D.what₂.places.ramIdx_pos w
    have hcoef : ∀ n, T.B.ec j w ((T.B.hL j w v k).charpoly.coeff n) ∈
        (algebraMap (T.B.Oc j w) (FractionRing (T.B.Oc j w))).range := by
      intro n
      have hprod := (IsAlgClosed.splits tC.charpoly).eq_prod_roots_of_monic (LinearMap.charpoly_monic tC)
      have hmem : tC.charpoly.coeff n ∈ NCov.intPrimeTo ℂ hl := by
        rw [hprod]; exact NCov.coeff_prod_mem _ _ hroots n
      rw [hCpoly, coeff_map] at hmem
      obtain ⟨d, hd0, hint⟩ := hmem
      set c := (T.B.hL j w v k).charpoly.coeff n
      have hint' : IsIntegral ℤ ((d : D.what₂.LL) * c) := by
        have e : (d : ℂ) * D.what₂.embLL c = D.what₂.embLL ((d : D.what₂.LL) * c) := by simp
        rw [e] at hint
        exact (isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective).1 hint
      have hv1 := NCov.nonneg_of_isIntegral (D.what₂.places.val w) hint'
      have hvd := NCov.val_eq_zero_of_not_dvd (D.what₂.places.val w) hl hvl d hd0
      rw [AddValuation.map_mul, hvd, zero_add] at hv1
      exact (T.B.ec_w j w c).1 hv1
    rw [hKpoly] at hroot
    refine NCov.mem_range_of_isRoot _ ((LinearMap.charpoly_monic _).map _) (fun n => ?_) hroot
    rw [coeff_map]; exact hcoef n

/- English proof (translation)
Introduce `j w i h v k s hvk hc hmem`. Take `⟨w', hover, hw'⟩` from `hmem`. Take `⟨-, e2⟩` from `(D.nd.locs_mem j w i).1 h`. Establish `hl : D.nd.l i = D.what₂.places.resChar w` using `by rw [← D.nd.w_l i, e2]`. Establish `hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → v ∈ placesOver D.host.E p`.

Introduce `p hp`. Establish `h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ w'.asIdeal` using `by rw [map_natCast]; exact hp`. Establish `h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal`. Rewrite using `[← hover]`. Conclude with `h1`.

Establish `h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.w.asIdeal`. Rewrite using `[← Ideal.mem_comap, s.w_under]`. Conclude with `h2`. Rewrite `h3` using `[map_natCast]`. Conclude with `(hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3`.

Break down `hw' with hQ | ⟨kk, hg⟩ | hpd` into its components or cases. Rewrite `hQ` using `[T.Q_eq j w i h]`. Establish `hsw : s.w ∈ T.B.Qc j w` using `T.B.Qc_over j w w' s.w hQ ⟨s.v, hover, s.w_under⟩`. Conclude with `hvk.2.2.2.1 (T.B.Qc_conj j w v s.w hsw hc)`. Apply `hvk.2.2.1` to reduce the goal to its premises.

Use `⟨?_, hvk.2.1⟩` and prove the remaining obligations. Establish `hv` using `hp _ hg`. Use `fin_cases kk`. Conclude with `Or.inl hv`. Conclude with `Or.inr (Or.inl hv)`.

Apply `hvk.2.2.1` to reduce the goal to its premises. Use `⟨?_, hvk.2.1⟩` and prove the remaining obligations. Rewrite `hpd` using `[hl]`. Conclude with `Or.inr (Or.inr (hp _ hpd))`.
-/
theorem genOutBad_of (T : NormalizedLocalCompatibility D M) : GenOutBad T := by
  intro j w i h v k s hvk hc hmem
  obtain ⟨w', hover, hw'⟩ := hmem
  obtain ⟨-, e2⟩ := (D.nd.locs_mem j w i).1 h
  have hl : D.nd.l i = D.what₂.places.resChar w := by rw [← D.nd.w_l i, e2]
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → v ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by simp)).2 h3
  rcases hw' with hQ | ⟨kk, hg⟩ | hpd
  · rw [T.Q_eq j w i h] at hQ
    have hsw : s.w ∈ T.B.Qc j w := T.B.Qc_over j w w' s.w hQ ⟨s.v, hover, s.w_under⟩
    exact hvk.2.2.2.1 (T.B.Qc_conj j w v s.w hsw hc)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · apply hvk.2.2.1
    refine ⟨?_, hvk.2.1⟩
    rw [hl] at hpd
    exact Or.inr (Or.inr (hp _ hpd))

end Formalism.L2
