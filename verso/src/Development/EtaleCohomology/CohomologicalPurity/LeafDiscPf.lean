import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
import Development.EtaleCohomology.KummerTheory.DictNormalPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.DiscPf

variable {R : Type} [CommRing R]

abbrev Cd (R : Type) [CommRing R] (P : PSh) : Cx R := (chains R).obj (disc.obj P)

abbrev e0 (R : Type) [CommRing R] (P : PSh) : (Cd R P).X (-((0 : ℕ) : ℤ)) ≅ (free R).obj P := chainsXIso R (disc.obj P) 0

/- English proof (translation)
The claim follows from `HomologicalComplex.isZero_extend_X ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat j (fun i h => by change (-(i : ℤ)) = j at h; omega)`.
-/
theorem isZero_pos (P : PSh) (j : ℤ) (hj : 0 < j) : IsZero ((Cd R P).X j) :=
  HomologicalComplex.isZero_extend_X ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat j
    (fun i h => by change (-(i : ℤ)) = j at h; omega)

/- English proof (translation)
Establish `h` using `LateralTheory.KummerTheory.chains_d R (disc.obj P) 0`. Establish `hs : (∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ (disc.obj P) i)) = 0`. Establish `: ∀ i : Fin (0 + 2), (free R).map (SimplicialObject.δ (disc.obj P) i) = 𝟙 _` using `fun i => (free R).map_id _`. Simplify using `only [this]`. Simplify using the standard rewrite rules.

Rewrite `h` using `[hs, zero_comp]`. Establish `: (chainsXIso R (disc.obj P) (0 + 1)).hom ≫ (chainsXIso R (disc.obj P) (0 + 1)).inv ≫ (Cd R P).d (-((0 + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) = 0` using `by rw [h, comp_zero]`. Simplify using `using this`.
-/
theorem d_one (P : PSh) : (Cd R P).d (-1) (-((0 : ℕ) : ℤ)) = 0 := by
  have h := LateralTheory.KummerTheory.chains_d R (disc.obj P) 0
  have hs : (∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ (disc.obj P) i)) = 0 := by
    have : ∀ i : Fin (0 + 2), (free R).map (SimplicialObject.δ (disc.obj P) i) = 𝟙 _ := fun i => (free R).map_id _
    simp only [this]
    simp
  rw [hs, zero_comp] at h
  have : (chainsXIso R (disc.obj P) (0 + 1)).hom ≫ (chainsXIso R (disc.obj P) (0 + 1)).inv ≫
      (Cd R P).d (-((0 + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) = 0 := by rw [h, comp_zero]
  simpa using this

def coch {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) : Cochain (Cd R P) K n :=
  Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((e0 R P).hom ≫ a) n

/- English proof (translation)
Use extensionality with `p q hpq`. Distinguish the cases in `hp : p = -((0 : ℕ) : ℤ)`. Substitute `hp` using the available equality. Take `rfl : q = n` from `by omega`. Simplify using `[coch, Cochain.single_v]`.

Simplify using `[coch, Cochain.single_v_eq_zero _ _ _ _ _ hp]`.
-/
theorem coch_add {K : Cx R} {n : ℤ} (P : PSh) (a b : (free R).obj P ⟶ K.X n) : coch P (a + b) = coch P a + coch P b := by
  ext p q hpq
  by_cases hp : p = -((0 : ℕ) : ℤ)
  · subst hp
    obtain rfl : q = n := by omega
    simp [coch, Cochain.single_v]
  · simp [coch, Cochain.single_v_eq_zero _ _ _ _ _ hp]

/- English proof (translation)
Rewrite using `[coch, Cochain.δ_single _ n (n + 1) rfl (-1) (n + 1) (by simp) rfl, d_one, zero_comp, Cochain.single_zero, smul_zero, add_zero, Category.assoc]`.
-/
theorem delta_coch {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) :
    δ n (n + 1) (coch P a) = Cochain.single (p := -((0 : ℕ) : ℤ)) ((e0 R P).hom ≫ a ≫ K.d n (n + 1)) (n + 1) := by
  rw [coch, Cochain.δ_single _ n (n + 1) rfl (-1) (n + 1) (by simp) rfl, d_one, zero_comp, Cochain.single_zero, smul_zero,
    add_zero, Category.assoc]

/- English proof (translation)
Rewrite using `[delta_coch, ha, comp_zero, Cochain.single_zero]`.
-/
theorem coch_cocycle {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    δ n (n + 1) (coch P a) = 0 := by
  rw [delta_coch, ha, comp_zero, Cochain.single_zero]

def cz {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) : Cocycle (Cd R P) K n :=
  ⟨coch P a, (Cocycle.mem_iff n (n + 1) rfl _).2 (coch_cocycle P a ha)⟩

open Classical in
def cl (K : Cx R) (n : ℤ) (P : PSh) (a : (free R).obj P ⟶ K.X n) : CohomologyClass (Cd R P) K n :=
  if ha : a ≫ K.d n (n + 1) = 0 then CohomologyClass.mk (cz P a ha) else 0

/- English proof (translation)
The claim follows from `dif_pos ha`.
-/
theorem cl_eq {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cl K n P a = CohomologyClass.mk (cz P a ha) := dif_pos ha

/- English proof (translation)
Establish `hab : (a + b) ≫ K.d n (n + 1) = 0` using `by rw [Preadditive.add_comp, ha, hb, add_zero]`. Rewrite using `[cl_eq _ _ ha, cl_eq _ _ hb, cl_eq _ _ hab, ← CohomologyClass.mk_add]`. Use `congr 1`. Conclude with `Cocycle.ext (coch_add P a b)`.
-/
theorem cl_add {K : Cx R} {n : ℤ} (P : PSh) (a b : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0)
    (hb : b ≫ K.d n (n + 1) = 0) : cl K n P (a + b) = cl K n P a + cl K n P b := by
  have hab : (a + b) ≫ K.d n (n + 1) = 0 := by rw [Preadditive.add_comp, ha, hb, add_zero]
  rw [cl_eq _ _ ha, cl_eq _ _ hb, cl_eq _ _ hab, ← CohomologyClass.mk_add]
  congr 1
  exact Cocycle.ext (coch_add P a b)

/- English proof (translation)
Rewrite using `[cl_eq _ _ ha, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨β, hβ⟩`. Use `⟨(e0 R P).inv ≫ β.v (-((0 : ℕ) : ℤ)) (n - 1) (by omega), ?_⟩` and prove the remaining obligations. Establish `h1` using `Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) n (by omega)`.

Rewrite `h1` using `[δ_v (n - 1) n (by omega) β _ n _ (n - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl, (isZero_pos P (-((0 : ℕ) : ℤ) + 1) (by omega)).eq_of_tgt ((Cd R P).d (-((0 : ℕ) : ℤ)) _) 0, zero_comp, smul_zero, add_zero]`. Establish `h2 : (cz P a ha).1.v (-((0 : ℕ) : ℤ)) n (by omega) = (e0 R P).hom ≫ a` using `Cochain.single_v _ _ _`. Rewrite `h1` using `[h2]`. Rewrite using `[Category.assoc, h1, Iso.inv_hom_id_assoc]`. Introduce and unpack `⟨b, rfl⟩`.

Use `⟨Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n - 1) ((e0 R P).hom ≫ b) (n - 1), ?_⟩` and prove the remaining obligations. Rewrite using `[Cochain.δ_single _ (n - 1) n (by omega) (-1) n (by simp) (by omega), d_one, zero_comp, Cochain.single_zero, smul_zero, add_zero, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem cl_zero_iff {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cl K n P a = 0 ↔ ∃ b, b ≫ K.d (n - 1) n = a := by
  rw [cl_eq _ _ ha, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨(e0 R P).inv ≫ β.v (-((0 : ℕ) : ℤ)) (n - 1) (by omega), ?_⟩
    have h1 := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) n (by omega)
    rw [δ_v (n - 1) n (by omega) β _ n _ (n - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl,
      (isZero_pos P (-((0 : ℕ) : ℤ) + 1) (by omega)).eq_of_tgt ((Cd R P).d (-((0 : ℕ) : ℤ)) _) 0, zero_comp, smul_zero, add_zero] at h1
    have h2 : (cz P a ha).1.v (-((0 : ℕ) : ℤ)) n (by omega) = (e0 R P).hom ≫ a := Cochain.single_v _ _ _
    rw [h2] at h1
    rw [Category.assoc, h1, Iso.inv_hom_id_assoc]
  · rintro ⟨b, rfl⟩
    refine ⟨Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n - 1) ((e0 R P).hom ≫ b) (n - 1), ?_⟩
    rw [Cochain.δ_single _ (n - 1) n (by omega) (-1) n (by simp) (by omega), d_one, zero_comp, Cochain.single_zero, smul_zero,
      add_zero, Category.assoc]
    rfl

/- English proof (translation)
Simplify using `only [chains, e0, chainsXIso, Functor.comp_map, Functor.comp_obj]`. Use `erw [HomologicalComplex.extendMap_f _ _ (i := 0) rfl]`. Use `erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Both sides reduce to the same expression.
-/
theorem etale_discrete_chains_degree_zero_iso_free_naturality (P' P : PSh) (f : P' ⟶ P) :
    ((chains R).map (disc.map f)).f (-((0 : ℕ) : ℤ)) ≫ (e0 R P).hom = (e0 R P').hom ≫ (free R).map f := by
  dsimp only [chains, e0, chainsXIso, Functor.comp_map, Functor.comp_obj]
  erw [HomologicalComplex.extendMap_f _ _ (i := 0) rfl]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/- English proof (translation)
Establish `ha' : ((free R).map f ≫ a) ≫ K.d n (n + 1) = 0` using `by rw [Category.assoc, ha, comp_zero]`. Rewrite using `[cl_eq _ _ ha, cl_eq _ _ ha', cpre_mk]`. Use `congr 1`. Apply `Cocycle.ext` to reduce the goal to its premises. Use `Cochain.ext _ _ (fun p q hpq => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `((Cochain.ofHom ((chains R).map (disc.map f))).comp (coch P a) (zero_add n)).v p q hpq = (coch P' _).v p q hpq`. Rewrite using `[Cochain.zero_cochain_comp_v, Cochain.ofHom_v]`. Distinguish the cases in `hp : p = -((0 : ℕ) : ℤ)`. Substitute `hp` using the available equality. Take `rfl : q = n` from `by omega`.

Simplify using `only [coch, Cochain.single_v]`. Rewrite using `[← Category.assoc, etale_discrete_chains_degree_zero_iso_free_naturality, Category.assoc]`. Simplify using `only [coch, Cochain.single_v_eq_zero _ _ _ _ _ hp, comp_zero]`.
-/
theorem cl_nat {K : Cx R} {n : ℤ} (P' P : PSh) (f : P' ⟶ P) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cpre (Cocycle.ofHom ((chains R).map (disc.map f))) K n n (zero_add n) (cl K n P a) = cl K n P' ((free R).map f ≫ a) := by
  have ha' : ((free R).map f ≫ a) ≫ K.d n (n + 1) = 0 := by rw [Category.assoc, ha, comp_zero]
  rw [cl_eq _ _ ha, cl_eq _ _ ha', cpre_mk]
  congr 1
  apply Cocycle.ext
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  change ((Cochain.ofHom ((chains R).map (disc.map f))).comp (coch P a) (zero_add n)).v p q hpq = (coch P' _).v p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  by_cases hp : p = -((0 : ℕ) : ℤ)
  · subst hp
    obtain rfl : q = n := by omega
    simp only [coch, Cochain.single_v]
    rw [← Category.assoc, etale_discrete_chains_degree_zero_iso_free_naturality, Category.assoc]
  · simp only [coch, Cochain.single_v_eq_zero _ _ _ _ _ hp, comp_zero]

end LateralTheory.CohomologicalPurity.Cl.DiscPf

namespace LateralTheory.CohomologicalPurity.Cl

open DiscPf in

def LeafDiscNrm : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ) (P : PSh)
  (z : Cocycle ((chains R).obj (disc.obj P)) K n),
  ∃ (a : (free R).obj P ⟶ K.X n) (β : Cochain ((chains R).obj (disc.obj P)) K (n - 1)),
    z.1 = Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((chainsXIso R (disc.obj P) 0).hom ≫ a) n + δ (n - 1) n β

open DiscPf in
/- English proof (translation)
Introduce `R _ K n`. Use `⟨cl K n, fun P a b ha hb => cl_add P a b ha hb, ?_, fun P a ha => cl_zero_iff P a ha, fun P' P f a ha => cl_nat P' P f a ha⟩` and prove the remaining obligations. Introduce `P x`. Take `⟨z, rfl⟩` from `CohomologyClass.mk_surjective x`. Take `⟨a, β, hz⟩` from `hN R K n P z`.

Establish `hz0 : δ n (n + 1) z.1 = 0` using `(Cocycle.mem_iff n (n + 1) rfl z.1).1 z.2`. Establish `hc : δ n (n + 1) (coch P a) = 0`. Use `hz0` as an intermediate fact. Rewrite `this` using `[hz, δ_add, δ_δ, add_zero]`. Conclude with `this`.

Establish `ha : a ≫ K.d n (n + 1) = 0`. Rewrite `hc` using `[delta_coch]`. Establish `h1` using `Cochain.congr_v hc (-((0 : ℕ) : ℤ)) (n + 1) (by omega)`. Rewrite `h1` using `[Cochain.single_v, Cochain.zero_v]`. Conclude with `(cancel_epi (e0 R P).hom).1 (h1.trans (comp_zero).symm)`.

Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[cl_eq _ _ ha, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]`. Use `⟨-β, ?_⟩` and prove the remaining obligations. Rewrite using `[δ_neg]`. Express the relevant statement in the definitionally equal form `_ = coch P a - z.1`.

Rewrite using `[hz]`. Unfold `coch`. Normalize the expressions using the abelian group laws.
-/
theorem LeafDisc_of (hN : LeafDiscNrm) : LeafDisc := by
  intro R _ K n
  refine ⟨cl K n, fun P a b ha hb => cl_add P a b ha hb, ?_, fun P a ha => cl_zero_iff P a ha,
    fun P' P f a ha => cl_nat P' P f a ha⟩
  intro P x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨a, β, hz⟩ := hN R K n P z
  have hz0 : δ n (n + 1) z.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl z.1).1 z.2
  have hc : δ n (n + 1) (coch P a) = 0 := by
    have := hz0
    rw [hz, δ_add, δ_δ, add_zero] at this
    exact this
  have ha : a ≫ K.d n (n + 1) = 0 := by
    rw [delta_coch] at hc
    have h1 := Cochain.congr_v hc (-((0 : ℕ) : ℤ)) (n + 1) (by omega)
    rw [Cochain.single_v, Cochain.zero_v] at h1
    exact (cancel_epi (e0 R P).hom).1 (h1.trans (comp_zero).symm)
  refine ⟨a, ha, ?_⟩
  rw [cl_eq _ _ ha, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨-β, ?_⟩
  rw [δ_neg]
  change _ = coch P a - z.1
  rw [hz]
  unfold coch
  abel

end LateralTheory.CohomologicalPurity.Cl
