import Development.EtaleCohomology.KummerTheory.BockCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedEpiPf
open LateralTheory.KummerTheory.BockCut

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (y : Sec F U) : Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

/- English proof (translation)
Substitute `hq` using the available equality. Establish `: Subsingleton (Sec (tw 1 i) V)` using `Module.subsingleton (ULift.{1} (ZMod 1)) _`. Conclude with `Subsingleton.elim (α := Sec (tw 1 i) V) x 0`.
-/
theorem sec_TZ_eq_zero {q : ℕ} (hq : q = 1) (i : ℤ) {V : Scheme.{0}} (x : Sec (TZ q i) V) : x = 0 := by
  subst hq
  have : Subsingleton (Sec (tw 1 i) V) := Module.subsingleton (ULift.{1} (ZMod 1)) _
  exact Subsingleton.elim (α := Sec (tw 1 i) V) x 0

/- English proof (translation)
Introduce `l _ c a hac i π hπ`. Take `⟨hall, hmono, -, -, htrans, -, -⟩` from `h_lb`. Establish `hl0 : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Establish `: NeZero (l ^ a)` using `⟨pow_ne_zero _ hl0⟩`. Establish `: NeZero (l ^ c)` using `⟨pow_ne_zero _ hl0⟩`.

Use `((h_me ℤ π).2.2.1).2 ?_` and prove the remaining obligations. Introduce `U y`. Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Apply `hall` to reduce the goal to its premises. Introduce `V g`.

Conclude with `⟨0, (sec_TZ_eq_zero (pow_zero l) i _).trans (sec_TZ_eq_zero (pow_zero l) i _).symm⟩`. It suffices to establish `key : ∀ y' : Sec (tw (l ^ a) i) U, Loc U fun V g => ∃ x : Sec (TZ (l ^ c) i) V, Sec.map π x = (Sec.res (F` using `tw (l ^ a) i) g y' : Sec (tw (l ^ a) i) V) from key y clear y`. Introduce `y`. Apply `htrans` to reduce the goal to its premises. Use `hmono _ _ _ ((h_tw (l ^ a) i).1 U y) ?_` and prove the remaining obligations.

Introduce `V g hd`. Break down `hd with h0 | ⟨ξ, d, hξ⟩` into its components or cases. Apply `hall` to reduce the goal to its premises. Introduce `W k`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Establish `e1 : Sec.res (F` using `tw (l ^ a) i) (k ≫ g) y = 0 := by`. Rewrite using `[res_comp, h0]`. Conclude with `map_zero ((tw (l ^ a) i).obj.map k.op).hom`. Establish `e2 : Sec.map π (0 : Sec (TZ (l ^ c) i) W) = 0` using `map_zero (π.hom.app (op W)).hom`. Conclude with `e2.trans e1.symm`.

Establish `hla : IsUnit ((l : Γ(V, ⊤)) ^ a)` using `by simpa using ξ.2.1`. Establish `hl : IsUnit (l : Γ(V, ⊤))` using `(isUnit_pow_iff ha.ne').1 hla`. Establish `hlc : IsUnit ((l ^ c : ℕ) : Γ(V, ⊤))` using `by simpa using hl.pow c`. Apply `htrans` to reduce the goal to its premises. Use `hmono _ _ _ ((h_pl (l ^ c) V).1 hlc) ?_` and prove the remaining obligations.

Introduce and unpack `W k ⟨ζ⟩`. Take `⟨ζ', hζ'⟩` from `(h_pb (l ^ c) Γ(W, ⊤)).2.2.2.2.2 (l ^ a) (pow_dvd_pow l hac) ζ`. Use `hmono _ _ _ ((h_tw (l ^ a) i).2.1 W ζ' (Sec.res (F := tw (l ^ a) i) k (Sec.res (F := tw (l ^ a) i) g y))) ?_` and prove the remaining obligations. Introduce and unpack `W' k' ⟨e, he⟩`. Use `beta_reduce`.

Use `⟨e • genZ i (ζ.map k'.appTop.hom), ?_⟩` and prove the remaining obligations. Establish `hr : (ζ'.map k'.appTop.hom).1 = (ζ.map k'.appTop.hom).1 ^ (l ^ c / l ^ a)` using `by show k'.appTop.hom ζ'.1 = (k'.appTop.hom ζ.1) ^ _`. Rewrite using `[hζ', map_pow]`. Establish `e3 : Sec.res (F` using `tw (l ^ a) i) ((k' ≫ k) ≫ g) y = e • twGen i (ζ'.map k'.appTop.hom) := by`. Rewrite using `[res_comp, res_comp, he]`.

Establish `e4 : Sec.map π (e • genZ i (ζ.map k'.appTop.hom)) = e • genZ i (ζ'.map k'.appTop.hom)` using `(map_nsmul (π.hom.app (op W')).hom e _).trans (congrArg (fun z => e • z) (hπ W' _ _ hr))`. Conclude with `e4.trans e3.symm`.
-/
theorem RedEpi_of (h_tw : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (h_pb : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (h_pl : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally) (h_me : LateralTheory.EtaleFoundations.EtaleSheafMonoEpiSectionCriteria)
    (h_lb : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : LateralTheory.KummerTheory.BockCut.RedEpi := by
  intro l _ c a hac i π hπ
  obtain ⟨hall, hmono, -, -, htrans, -, -⟩ := h_lb
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ a) := ⟨pow_ne_zero _ hl0⟩
  have : NeZero (l ^ c) := ⟨pow_ne_zero _ hl0⟩
  refine ((h_me ℤ π).2.2.1).2 ?_
  intro U y
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · apply hall
    intro V g
    exact ⟨0, (sec_TZ_eq_zero (pow_zero l) i _).trans (sec_TZ_eq_zero (pow_zero l) i _).symm⟩
  · suffices key : ∀ y' : Sec (tw (l ^ a) i) U, Loc U fun V g =>
        ∃ x : Sec (TZ (l ^ c) i) V, Sec.map π x = (Sec.res (F := tw (l ^ a) i) g y' : Sec (tw (l ^ a) i) V) from key y
    clear y
    intro y
    apply htrans
    refine hmono _ _ _ ((h_tw (l ^ a) i).1 U y) ?_
    intro V g hd
    rcases hd with h0 | ⟨ξ, d, hξ⟩
    · apply hall
      intro W k
      refine ⟨0, ?_⟩
      have e1 : Sec.res (F := tw (l ^ a) i) (k ≫ g) y = 0 := by
        rw [res_comp, h0]
        exact map_zero ((tw (l ^ a) i).obj.map k.op).hom
      have e2 : Sec.map π (0 : Sec (TZ (l ^ c) i) W) = 0 := map_zero (π.hom.app (op W)).hom
      exact e2.trans e1.symm
    · have hla : IsUnit ((l : Γ(V, ⊤)) ^ a) := by simpa using ξ.2.1
      have hl : IsUnit (l : Γ(V, ⊤)) := (isUnit_pow_iff ha.ne').1 hla
      have hlc : IsUnit ((l ^ c : ℕ) : Γ(V, ⊤)) := by simpa using hl.pow c
      apply htrans
      refine hmono _ _ _ ((h_pl (l ^ c) V).1 hlc) ?_
      rintro W k ⟨ζ⟩
      obtain ⟨ζ', hζ'⟩ := (h_pb (l ^ c) Γ(W, ⊤)).2.2.2.2.2 (l ^ a) (pow_dvd_pow l hac) ζ
      refine hmono _ _ _ ((h_tw (l ^ a) i).2.1 W ζ' (Sec.res (F := tw (l ^ a) i) k (Sec.res (F := tw (l ^ a) i) g y))) ?_
      rintro W' k' ⟨e, he⟩
      beta_reduce
      refine ⟨e • genZ i (ζ.map k'.appTop.hom), ?_⟩
      have hr : (ζ'.map k'.appTop.hom).1 = (ζ.map k'.appTop.hom).1 ^ (l ^ c / l ^ a) := by
        show k'.appTop.hom ζ'.1 = (k'.appTop.hom ζ.1) ^ _
        rw [hζ', map_pow]
      have e3 : Sec.res (F := tw (l ^ a) i) ((k' ≫ k) ≫ g) y = e • twGen i (ζ'.map k'.appTop.hom) := by
        rw [res_comp, res_comp, he]
      have e4 : Sec.map π (e • genZ i (ζ.map k'.appTop.hom)) = e • genZ i (ζ'.map k'.appTop.hom) :=
        (map_nsmul (π.hom.app (op W')).hom e _).trans (congrArg (fun z => e • z) (hπ W' _ _ hr))
      exact e4.trans e3.symm

end LateralTheory.KummerTheory.RedEpiPf
