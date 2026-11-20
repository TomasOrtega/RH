import Mathlib
import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
import Formalism.LocalToGlobal.Columns.InputsLemmas
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalRingCardinality.MinkMEqMinkowskiNumber

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.L2.Col

section One

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def autLcm : ℕ := sInf {D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D}

variable {E n}

/- English proof (translation)
Establish `hne : ({D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D} : Set ℕ).Nonempty` using `⟨D, hD, h⟩`. Conclude with `Nat.sInf_mem hne`.
-/
theorem autLcm_mem {D : ℕ} (hD : 0 < D) (h : ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D) :
    0 < autLcm E n ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ autLcm E n := by
  have hne : ({D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D} : Set ℕ).Nonempty := ⟨D, hD, h⟩
  exact Nat.sInf_mem hne

/- English proof (translation)
Take `⟨hpos, hdvd⟩` from `autLcm_mem hD h`. Establish `hg : 0 < Nat.gcd (autLcm E n) D` using `Nat.gcd_pos_of_pos_left _ hpos`. Establish `hmem : Nat.gcd (autLcm E n) D ∈ {D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D}` using `⟨hg, fun N => Nat.dvd_gcd (hdvd N) (h N)⟩`. Establish `hle : autLcm E n ≤ Nat.gcd (autLcm E n) D` using `Nat.sInf_le hmem`. Establish `hge : Nat.gcd (autLcm E n) D ≤ autLcm E n` using `Nat.le_of_dvd hpos (Nat.gcd_dvd_left _ _)`.

Establish `heq : Nat.gcd (autLcm E n) D = autLcm E n` using `le_antisymm hge hle`. Rewrite using `[← heq]`. Conclude with `Nat.gcd_dvd_right _ _`.
-/
theorem autLcm_dvd {D : ℕ} (hD : 0 < D) (h : ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D) : autLcm E n ∣ D := by
  obtain ⟨hpos, hdvd⟩ := autLcm_mem hD h
  have hg : 0 < Nat.gcd (autLcm E n) D := Nat.gcd_pos_of_pos_left _ hpos
  have hmem : Nat.gcd (autLcm E n) D ∈ {D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D} :=
    ⟨hg, fun N => Nat.dvd_gcd (hdvd N) (h N)⟩
  have hle : autLcm E n ≤ Nat.gcd (autLcm E n) D := Nat.sInf_le hmem
  have hge : Nat.gcd (autLcm E n) D ≤ autLcm E n := Nat.le_of_dvd hpos (Nat.gcd_dvd_left _ _)
  have heq : Nat.gcd (autLcm E n) D = autLcm E n := le_antisymm hge hle
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

/- English proof (translation)
Set `φ : autU E n N →* GL (Fin n) E` to `(ufGL E n).comp (autU E n N).subtype`. Establish `hφ : Function.Injective φ` using `fun a b hab => Subtype.ext (Subtype.ext ((toGLm E n).injective hab))`. Establish `hfin : Finite (autU E n N)` using `finite_autU hE N`. Establish `hfin' : Finite φ.range` using `Finite.of_equiv _ (MonoidHom.ofInjective hφ).toEquiv`. Establish `hst : φ.range ≤ Formalism.UG.stabGL N.1`.

Introduce and unpack `_ ⟨a, rfl⟩ x`. Establish `ha : gmap (a.1 : UF E n).1 N.1 = N.1` using `congrArg Subtype.val a.2`. Use `show x ∈ _ ↔ ((toGLm E n (a.1 : UF E n).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).mulVec x ∈ _`. Rewrite using `[toGLm_mulVec]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Rewrite using `[← ha]`. Conclude with `Submodule.mem_map_of_mem hx`. Introduce `hx`. Rewrite `hx` using `[← ha]`.

Take `⟨y, hy, e⟩` from `hx`. Establish `: y = x` using `(a.1 : UF E n).1.injective e`. Rewrite using `[← this]` and apply the resulting hypothesis. Establish `h1` using `mk_card_dvd minkowskiBound_holds N.1 N.2.1 φ.range hfin' hst`. Rewrite `h1` using `[← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]`.

Conclude with `h1`.
-/
theorem card_autU_dvd_minkM (hE : PosStar E) (N : UniLat E n) :
    Nat.card (autU E n N) ∣ minkM (Module.finrank ℚ E * n) := by
  let φ : autU E n N →* GL (Fin n) E := (ufGL E n).comp (autU E n N).subtype
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext ((toGLm E n).injective hab))
  have hfin : Finite (autU E n N) := finite_autU hE N
  have hfin' : Finite φ.range := Finite.of_equiv _ (MonoidHom.ofInjective hφ).toEquiv
  have hst : φ.range ≤ Formalism.UG.stabGL N.1 := by
    rintro _ ⟨a, rfl⟩ x
    have ha : gmap (a.1 : UF E n).1 N.1 = N.1 := congrArg Subtype.val a.2
    show x ∈ _ ↔ ((toGLm E n (a.1 : UF E n).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).mulVec x ∈ _
    rw [toGLm_mulVec]
    constructor
    · intro hx
      rw [← ha]
      exact Submodule.mem_map_of_mem hx
    · intro hx
      rw [← ha] at hx
      obtain ⟨y, hy, e⟩ := hx
      have : y = x := (a.1 : UF E n).1.injective e
      rwa [← this]
  have h1 := mk_card_dvd minkowskiBound_holds N.1 N.2.1 φ.range hfin' hst
  rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv] at h1
  exact h1

/- English proof (translation)
The claim follows from `(autLcm_mem (minkM_pos _) (card_autU_dvd_minkM hE)).1`.
-/
theorem autLcm_pos (hE : PosStar E) : 0 < autLcm E n := (autLcm_mem (minkM_pos _) (card_autU_dvd_minkM hE)).1

/- English proof (translation)
The claim follows from `(autLcm_mem (minkM_pos _) (card_autU_dvd_minkM hE)).2 N`.
-/
theorem card_autU_dvd_autLcm (hE : PosStar E) (N : UniLat E n) : Nat.card (autU E n N) ∣ autLcm E n := (autLcm_mem (minkM_pos _) (card_autU_dvd_minkM hE)).2 N

/- English proof (translation)
The claim follows from `autLcm_dvd (minkM_pos _) (card_autU_dvd_minkM hE)`.
-/
theorem autLcm_dvd_minkM (hE : PosStar E) : autLcm E n ∣ minkM (Module.finrank ℚ E * n) := autLcm_dvd (minkM_pos _) (card_autU_dvd_minkM hE)

/- English proof (translation)
Apply `Nat.dvd_antisymm` to reduce the goal to its premises. Apply `autLcm_dvd` to reduce the goal to its premises. Apply `Nat.pos_of_ne_zero` to reduce the goal to its premises. Rewrite using `[Ne, Finset.lcm_eq_zero_iff]`. Introduce and unpack `⟨c, -, hc⟩`.

Use `haveI := finite_autU hE (Quotient.out c)`. Conclude with `(Nat.card_pos (α := autU E n (Quotient.out c))).ne' hc`. Introduce `N`. Establish `hrel` using `Quotient.exact (Quotient.out_eq (Quotient.mk'' N : UniCl E n))`. Establish `hc : Nat.card (autU E n (Quotient.out (Quotient.mk'' N : UniCl E n))) = Nat.card (autU E n N)` using `Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel hrel).toEquiv`.

Rewrite using `[← hc]`. Conclude with `Finset.dvd_lcm (Finset.mem_univ _)`. Conclude with `Finset.lcm_dvd fun c _ => card_autU_dvd_autLcm hE _`.
-/
theorem autLcm_eq_lcm (hE : PosStar E) [Fintype (UniCl E n)] :
    autLcm E n = Finset.univ.lcm fun c : UniCl E n => Nat.card (autU E n (Quotient.out c)) := by
  classical
  apply Nat.dvd_antisymm
  · apply autLcm_dvd
    · apply Nat.pos_of_ne_zero
      rw [Ne, Finset.lcm_eq_zero_iff]
      rintro ⟨c, -, hc⟩
      haveI := finite_autU hE (Quotient.out c)
      exact (Nat.card_pos (α := autU E n (Quotient.out c))).ne' hc
    · intro N
      have hrel := Quotient.exact (Quotient.out_eq (Quotient.mk'' N : UniCl E n))
      have hc : Nat.card (autU E n (Quotient.out (Quotient.mk'' N : UniCl E n))) = Nat.card (autU E n N) :=
        Nat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel hrel).toEquiv
      rw [← hc]
      exact Finset.dvd_lcm (Finset.mem_univ _)
  · exact Finset.lcm_dvd fun c _ => card_autU_dvd_autLcm hE _

def UniLat.til (N : UniLat E n) : UniLat E (n + 1) := ⟨tilN N.1, tilN_lattice N.2.1, tilN_unimodular N.2.2⟩

def autU_til (N : UniLat E n) : autU E n N →* autU E (n + 1) N.til :=
  (extU.comp (autU E n N).subtype).codRestrict _ fun a => by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    show gmap (extE (a.1 : UF E n).1) (tilN N.1) = tilN N.1
    rw [← tilN_gmap]
    exact congrArg tilN (congrArg Subtype.val a.2)

/- English proof (translation)
Introduce `a b hab`. Establish `h1 : extE (a.1 : UF E n).1 = extE (b.1 : UF E n).1` using `congrArg (fun u : autU E (n + 1) N.til => (u.1 : UF E (n + 1)).1) hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearEquiv.ext` to reduce the goal to its premises.

Introduce `x`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : Sp E (n + 1), initL E n y = x := by`. Use `⟨Fin.snoc (α := fun _ => E) x 0, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(fun i : Fin n => (Fin.snoc (α := fun _ => E) x 0 : Fin (n + 1) → E) (Fin.castSucc i)) = x`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Substitute `hy` using the available equality. Combine the equalities or inequalities in the displayed calculation.
-/
theorem autU_til_injective (N : UniLat E n) : Function.Injective (autU_til N) := by
  intro a b hab
  have h1 : extE (a.1 : UF E n).1 = extE (b.1 : UF E n).1 :=
    congrArg (fun u : autU E (n + 1) N.til => (u.1 : UF E (n + 1)).1) hab
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, hy⟩ : ∃ y : Sp E (n + 1), initL E n y = x := by
    refine ⟨Fin.snoc (α := fun _ => E) x 0, ?_⟩
    change (fun i : Fin n => (Fin.snoc (α := fun _ => E) x 0 : Fin (n + 1) → E) (Fin.castSucc i)) = x
    funext i
    simp
  subst hy
  calc (a.1 : UF E n).1 (initL E n y) = initL E n (extE (a.1 : UF E n).1 y) := (initL_extE _ _).symm
    _ = initL E n (extE (b.1 : UF E n).1 y) := by rw [h1]
    _ = (b.1 : UF E n).1 (initL E n y) := initL_extE _ _

/- English proof (translation)
The claim follows from `autLcm_dvd (autLcm_pos (E := E) (n := n + 1) hE) fun N => (Subgroup.card_dvd_of_injective (autU_til N) (autU_til_injective N)).trans (card_autU_dvd_autLcm hE N.til)`.
-/
theorem autLcm_dvd_succ (hE : PosStar E) : autLcm E n ∣ autLcm E (n + 1) := autLcm_dvd (autLcm_pos (E := E) (n := n + 1) hE) fun N =>
    (Subgroup.card_dvd_of_injective (autU_til N) (autU_til_injective N)).trans (card_autU_dvd_autLcm hE N.til)

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `refl => exact dvd_rfl`. Consider the case `step _ ih => exact ih.trans (autLcm_dvd_succ hE)`.
-/
theorem autLcm_mono (hE : PosStar E) {n n' : ℕ} (h : n ≤ n') : autLcm E n ∣ autLcm E n' := by
  induction h with
  | refl => exact dvd_rfl
  | step _ ih => exact ih.trans (autLcm_dvd_succ hE)

end One

section DGam

def dGamRanks (R : Ranks) : Finset ℕ :=
  (Finset.Icc 1 R.m).image R.N ∪ {R.rankX', R.rankY (R.m - 1), R.nV}

def dGamAut (X : Fields) (R : Ranks) : ℕ := (dGamRanks R).lcm fun n => autLcm X.E n

variable {X : Fields} {R : Ranks}

/- English proof (translation)
Simplify using `only [Ranks.N]`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _`.
-/
theorem dga_N_mono (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  simp only [Ranks.N]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

/- English proof (translation)
Establish `hm` using `R.two_le_m`. Establish `hX : R.rankX' ≤ R.N R.m`. Simplify using `only [Ranks.rankX', Ranks.r, Ranks.N, Nat.mul_succ]`. Use linear arithmetic over natural numbers and integers. Establish `hY : R.rankY (R.m - 1) ≤ R.N R.m`.

Establish `h1 : (R.m - 1) * R.t ≤ R.m * R.t` using `Nat.mul_le_mul_right _ (Nat.sub_le _ _)`. Simplify using `only [Ranks.rankY, Ranks.r, Ranks.N, Nat.mul_succ]`. Use linear arithmetic over natural numbers and integers. Establish `hV : R.nV ≤ R.N R.m`. Establish `h2 : 1 * R.t ≤ R.m * R.t` using `Nat.mul_le_mul_right _ (by omega)`.

Simplify using `only [Ranks.nV, Ranks.r, Ranks.N, Nat.mul_succ]`. Use linear arithmetic over natural numbers and integers. Unfold `dGamRanks at hn`. Simplify using `only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hn`. Break down `hn with ⟨j, ⟨_, hj⟩, rfl⟩ | rfl | rfl | rfl` into its components or cases.

Conclude with `dga_N_mono R hj`. Conclude with `hX`. Conclude with `hY`. Conclude with `hV`.
-/
theorem dGamRanks_le (R : Ranks) {n : ℕ} (hn : n ∈ dGamRanks R) : n ≤ R.N R.m := by
  have hm := R.two_le_m
  have hX : R.rankX' ≤ R.N R.m := by
    simp only [Ranks.rankX', Ranks.r, Ranks.N, Nat.mul_succ]
    omega
  have hY : R.rankY (R.m - 1) ≤ R.N R.m := by
    have h1 : (R.m - 1) * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    simp only [Ranks.rankY, Ranks.r, Ranks.N, Nat.mul_succ]
    omega
  have hV : R.nV ≤ R.N R.m := by
    have h2 : 1 * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ (by omega)
    simp only [Ranks.nV, Ranks.r, Ranks.N, Nat.mul_succ]
    omega
  unfold dGamRanks at hn
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hn
  rcases hn with ⟨j, ⟨_, hj⟩, rfl⟩ | rfl | rfl | rfl
  · exact dga_N_mono R hj
  · exact hX
  · exact hY
  · exact hV

/- English proof (translation)
Establish `hm` using `R.two_le_m`. Unfold `dGamRanks`. Apply `Finset.mem_union_left` to reduce the goal to its premises. Conclude with `Finset.mem_image.2 ⟨R.m, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, rfl⟩`.
-/
theorem N_m_mem_dGamRanks (R : Ranks) : R.N R.m ∈ dGamRanks R := by
  have hm := R.two_le_m
  unfold dGamRanks
  apply Finset.mem_union_left
  exact Finset.mem_image.2 ⟨R.m, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, rfl⟩

/- English proof (translation)
Establish `hE` using `posStar_of_ok hX`. Apply `Nat.dvd_antisymm` to reduce the goal to its premises. Conclude with `Finset.lcm_dvd fun n hn => autLcm_mono hE (dGamRanks_le R hn)`. Conclude with `Finset.dvd_lcm (N_m_mem_dGamRanks R)`.
-/
theorem dGamAut_eq (hX : X.Ok) : dGamAut X R = autLcm X.E (R.N R.m) := by
  have hE := posStar_of_ok hX
  apply Nat.dvd_antisymm
  · exact Finset.lcm_dvd fun n hn => autLcm_mono hE (dGamRanks_le R hn)
  · exact Finset.dvd_lcm (N_m_mem_dGamRanks R)

/- English proof (translation)
Rewrite using `[dGamAut_eq hX]`. Conclude with `autLcm_pos (posStar_of_ok hX)`.
-/
theorem dGamAut_pos (hX : X.Ok) : 0 < dGamAut X R := by
  rw [dGamAut_eq hX]
  exact autLcm_pos (posStar_of_ok hX)

/- English proof (translation)
Rewrite using `[dGamAut_eq hX]`. Conclude with `autLcm_mono (posStar_of_ok hX) hn`.
-/
theorem autLcm_dvd_dGamAut (hX : X.Ok) {n : ℕ} (hn : n ≤ R.N R.m) : autLcm X.E n ∣ dGamAut X R := by
  rw [dGamAut_eq hX]
  exact autLcm_mono (posStar_of_ok hX) hn

/- English proof (translation)
The claim follows from `(card_autU_dvd_autLcm (posStar_of_ok hX) N).trans (autLcm_dvd_dGamAut hX hn)`.
-/
theorem card_autU_dvd_dGamAut (hX : X.Ok) {n : ℕ} (hn : n ≤ R.N R.m) (N : UniLat X.E n) :
    Nat.card (autU X.E n N) ∣ dGamAut X R := (card_autU_dvd_autLcm (posStar_of_ok hX) N).trans (autLcm_dvd_dGamAut hX hn)

/- English proof (translation)
Conclude with `hX.finrank_E`.
-/
theorem dga_finrank (hX : X.Ok) : Module.finrank ℚ X.E = 2 * X.f := by
  exact hX.finrank_E

/- English proof (translation)
Rewrite using `[dGamAut_eq hX]`. Establish `h` using `autLcm_dvd_minkM (E := X.E) (n := R.N R.m) (posStar_of_ok hX)`. Rewrite `h` using `[dga_finrank hX]`. Then use the resulting hypothesis.
-/
theorem dGamAut_dvd_minkM (hX : X.Ok) : dGamAut X R ∣ minkM (2 * X.f * R.N R.m) := by
  rw [dGamAut_eq hX]
  have h := autLcm_dvd_minkM (E := X.E) (n := R.N R.m) (posStar_of_ok hX)
  rwa [dga_finrank hX] at h

/- English proof (translation)
The claim follows from `prime_le_of_dvd_minkM hp (h.trans (dGamAut_dvd_minkM hX))`.
-/
theorem dGamAut_prime_le (hX : X.Ok) {p : ℕ} (hp : p.Prime) (h : p ∣ dGamAut X R) : p ≤ 2 * X.f * R.N R.m + 1 := prime_le_of_dvd_minkM hp (h.trans (dGamAut_dvd_minkM hX))

end DGam

section Stab

variable {X : Fields} {R : Ranks} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

/- English proof (translation)
Set `φ : MulAction.stabilizer (formGSD C Λ).G d →* autU X.E n d.lat` to `((MonoidHom.fst (UF X.E n) ↥Λ.grp).comp (MulAction.stabilizer (formGSD C Λ).G d).subtype).codRestrict _ fun a => by`. Rewrite using `[MulAction.mem_stabilizer_iff]`. Conclude with `congrArg DecoSet.lat a.2`. Use `Subgroup.card_dvd_of_injective φ fun a b hab => ?_` and prove the remaining obligations. Establish `h1 : (a.1.1 : UF X.E n) = b.1.1` using `congrArg Subtype.val hab`.

Conclude with `Subtype.ext (formGSD_stab_inj C Λ d a.2 b.2 h1)`.
-/
theorem formGSD_stab_dvd_autU (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) (d : DecoSet X.E n ST SG) :
    Nat.card (MulAction.stabilizer (formGSD C Λ).G d) ∣ Nat.card (autU X.E n d.lat) := by
  let φ : MulAction.stabilizer (formGSD C Λ).G d →* autU X.E n d.lat :=
    ((MonoidHom.fst (UF X.E n) ↥Λ.grp).comp (MulAction.stabilizer (formGSD C Λ).G d).subtype).codRestrict _ fun a => by
      rw [MulAction.mem_stabilizer_iff]
      exact congrArg DecoSet.lat a.2
  refine Subgroup.card_dvd_of_injective φ fun a b hab => ?_
  have h1 : (a.1.1 : UF X.E n) = b.1.1 := congrArg Subtype.val hab
  exact Subtype.ext (formGSD_stab_inj C Λ d a.2 b.2 h1)

/- English proof (translation)
The claim follows from `(formGSD_stab_dvd_autU C Λ d).trans (card_autU_dvd_dGamAut hX hn _)`.
-/
theorem formGSD_stab_dvd_dGamAut (hX : X.Ok) (hn : n ≤ R.N R.m) (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG)
    (d : DecoSet X.E n ST SG) : Nat.card (MulAction.stabilizer (formGSD C Λ).G d) ∣ dGamAut X R := (formGSD_stab_dvd_autU C Λ d).trans (card_autU_dvd_dGamAut hX hn _)

/- English proof (translation)
Establish `hda : ((a.1, (a.2.1 : GLG X.E n SG)) • p.deco : DecoSet X.E n ST SG) = p.deco` using `congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) ha`. Establish `hdb : ((b.1, (b.2.1 : GLG X.E n SG)) • p.deco : DecoSet X.E n ST SG) = p.deco` using `congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) hb`. Establish `h1` using `DecoSet.stab_fst_injective p.deco hda hdb hab`. Establish `h2 : (a.2.1 : GLG X.E n SG) = b.2.1` using `congrArg Prod.snd h1`. Establish `h3 : ∀ P : Q, (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = (((b.2.2 : GLQ X.E n Q) P)⁻¹).1`.

Introduce `P`. Establish `ea : a.1.1 * p.fr P * (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P` using `congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) ha`. Establish `eb : b.1.1 * p.fr P * (((b.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P` using `congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) hb`. Rewrite `eb` using `[← hab]`. Conclude with `mul_left_cancel (ea.trans eb.symm)`.

Use `Prod.ext hab (Prod.ext (Subtype.ext h2) (Subtype.ext (funext fun P => ?_)))` and prove the remaining obligations. Conclude with `inv_injective (Subtype.ext (h3 P))`.
-/
theorem dga_frm_stab_inj (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) {a b : FrmG Λ Θ}
    (ha : a • p = p) (hb : b • p = p) (hab : a.1 = b.1) : a = b := by
  have hda : ((a.1, (a.2.1 : GLG X.E n SG)) • p.deco : DecoSet X.E n ST SG) = p.deco :=
    congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) ha
  have hdb : ((b.1, (b.2.1 : GLG X.E n SG)) • p.deco : DecoSet X.E n ST SG) = p.deco :=
    congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) hb
  have h1 := DecoSet.stab_fst_injective p.deco hda hdb hab
  have h2 : (a.2.1 : GLG X.E n SG) = b.2.1 := congrArg Prod.snd h1
  have h3 : ∀ P : Q, (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = (((b.2.2 : GLQ X.E n Q) P)⁻¹).1 := by
    intro P
    have ea : a.1.1 * p.fr P * (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P :=
      congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) ha
    have eb : b.1.1 * p.fr P * (((b.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P :=
      congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) hb
    rw [← hab] at eb
    exact mul_left_cancel (ea.trans eb.symm)
  refine Prod.ext hab (Prod.ext (Subtype.ext h2) (Subtype.ext (funext fun P => ?_)))
  exact inv_injective (Subtype.ext (h3 P))

/- English proof (translation)
Set `φ : MulAction.stabilizer (frmGSD C Λ Θ).G p →* autU X.E n p.deco.lat` to `((MonoidHom.fst (UF X.E n) (↥Λ.grp × ↥Θ.grp)).comp (MulAction.stabilizer (frmGSD C Λ Θ).G p).subtype).codRestrict _ fun a => by`. Rewrite using `[MulAction.mem_stabilizer_iff]`. Conclude with `Subtype.ext (congrArg (fun q : DecoF X.E n ST SG Q => q.1.1.1.N) a.2)`. Use `Subgroup.card_dvd_of_injective φ fun a b hab => ?_` and prove the remaining obligations. Establish `h1 : (a.1.1 : UF X.E n) = b.1.1` using `congrArg Subtype.val hab`.

Conclude with `Subtype.ext (dga_frm_stab_inj Λ Θ p a.2 b.2 h1)`.
-/
theorem frmGSD_stab_dvd_autU (C : CoefPk X n (DecoF X.E n ST SG Q)) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)
    (p : DecoF X.E n ST SG Q) :
    Nat.card (MulAction.stabilizer (frmGSD C Λ Θ).G p) ∣ Nat.card (autU X.E n p.deco.lat) := by
  let φ : MulAction.stabilizer (frmGSD C Λ Θ).G p →* autU X.E n p.deco.lat :=
    ((MonoidHom.fst (UF X.E n) (↥Λ.grp × ↥Θ.grp)).comp (MulAction.stabilizer (frmGSD C Λ Θ).G p).subtype).codRestrict _ fun a => by
      rw [MulAction.mem_stabilizer_iff]
      exact Subtype.ext (congrArg (fun q : DecoF X.E n ST SG Q => q.1.1.1.N) a.2)
  refine Subgroup.card_dvd_of_injective φ fun a b hab => ?_
  have h1 : (a.1.1 : UF X.E n) = b.1.1 := congrArg Subtype.val hab
  exact Subtype.ext (dga_frm_stab_inj Λ Θ p a.2 b.2 h1)

/- English proof (translation)
The claim follows from `(frmGSD_stab_dvd_autU C Λ Θ p).trans (card_autU_dvd_dGamAut hX hn _)`.
-/
theorem frmGSD_stab_dvd_dGamAut (hX : X.Ok) (hn : n ≤ R.N R.m) (C : CoefPk X n (DecoF X.E n ST SG Q)) (Λ : LevFam X.E X.K n SG)
    (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) :
    Nat.card (MulAction.stabilizer (frmGSD C Λ Θ).G p) ∣ dGamAut X R := (frmGSD_stab_dvd_autU C Λ Θ p).trans (card_autU_dvd_dGamAut hX hn _)

/- English proof (translation)
Apply `Subgroup.card_dvd_of_le` to reduce the goal to its premises. Introduce `g hg`. Rewrite `hg`, the goal using `[MulAction.mem_stabilizer_iff]`. Conclude with `congrArg (fun q => q.1.1) hg`.
-/
theorem stab_pair_dvd {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} (Y : Cpl S) (p : Y.Pts) :
    Nat.card (MulAction.stabilizer S.G p) ∣ Nat.card (MulAction.stabilizer S.G p.1.1) := by
  apply Subgroup.card_dvd_of_le
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  exact congrArg (fun q => q.1.1) hg

/- English proof (translation)
The claim follows from `(stab_pair_dvd Y p).trans (h p.1.1)`.
-/
theorem stab_pair_dvd_of {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K} (Y : Cpl S) {D : ℕ}
    (h : ∀ d : S.D, Nat.card (MulAction.stabilizer S.G d) ∣ D) (p : Y.Pts) : Nat.card (MulAction.stabilizer S.G p) ∣ D := (stab_pair_dvd Y p).trans (h p.1.1)

end Stab

end Formalism.L2.Col
