module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSystemRealStructure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

section Fibre

open GlobalTheory.NearFibreIso

theorem near_isIso_of_isProper_of_finitePresentation {R : Type} [CommRing R] {Y X : Scheme.{0}} (s : X ⟶ Sp R)
    (f : Y ⟶ X) (K : Type) [Field K] [Algebra R K] [IsProper f]
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation (f ≫ s)] [Flat (f ≫ s)]
    [IsIso (pullback.snd f (pullback.fst s (spMap (algebraMap R K))))]
    (x : X) (hx : RingHom.ker (algebraMap R K) = (s x).asIdeal) :
    Near f (MorphismProperty.isomorphisms _) x := by
  obtain ⟨T, T', g, g', f', H, _, ⟨y, rfl⟩, hQ⟩ := near_isFinite s f K x hx
  have := isIso_fibre_of_pullback s f (spMap (algebraMap R K)) H
  obtain ⟨U, U', k, k', f'', H', _, ⟨z, rfl⟩, hQ'⟩ :=
    near_isClosedImmersion (g ≫ s) f' K y (by rw [Scheme.Hom.comp_apply]; exact hx)
  have H'' := H'.paste_vert H
  have := isIso_fibre_of_pullback s f (spMap (algebraMap R K)) H''
  have : IsOpenImmersion (k' ≫ g') :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) H'' inferInstance
  have : Flat (f'' ≫ (k ≫ g) ≫ s) := by
    rw [H''.w_assoc]; infer_instance
  have : LocallyOfFinitePresentation (f'' ≫ (k ≫ g) ≫ s) := by
    rw [H''.w_assoc]; infer_instance
  have h := GlobalTheory.AbMonoIsoAny.near_isIso_of_finitePresentation ((k ≫ g) ≫ s) f'' K z
    (by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hx)
  have h' := Near.of_pullback f H'' h
  rwa [Scheme.Hom.comp_apply] at h'

theorem isIso_of_geometric_fibres {S X Y : Scheme.{0}} (p : X ⟶ S) (f : Y ⟶ X) [IsProper f]
    [LocallyOfFinitePresentation p] [LocallyOfFinitePresentation (f ≫ p)] [Flat (f ≫ p)]
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso (pullback.snd f (pullback.fst p t))) :
    IsIso f := by
  have hn : ∀ y : X, Near f (MorphismProperty.isomorphisms _) y := by
    intro y
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (p y)) isOpen_univ
    replace hU : IsAffineOpen U := hU
    let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
    obtain ⟨z, hz⟩ : p y ∈ Set.range j := by rw [hU.range_fromSpec]; exact hyU
    let gX := pullback.fst p j
    let s := pullback.snd p j
    let f' := pullback.snd f gX
    have HX := IsPullback.of_hasPullback p j
    have HY := IsPullback.of_hasPullback f gX
    have HYS := HY.paste_vert HX
    obtain ⟨y', hy', hy's⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := j) y z hz.symm
    have : Flat (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : LocallyOfFinitePresentation (f' ≫ s) := MorphismProperty.of_isPullback HYS ‹_›
    have : IsProper f' := MorphismProperty.of_isPullback HY (inferInstanceAs (IsProper f))
    have : (s y').asIdeal.IsPrime := (s y').isPrime
    let K := AlgebraicClosure (s y').asIdeal.ResidueField
    have hK : RingHom.ker (algebraMap Γ(S, U) K) = (s y').asIdeal := by
      rw [IsScalarTower.algebraMap_eq Γ(S, U) (s y').asIdeal.ResidueField K, ← RingHom.comap_ker,
        (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (s y').asIdeal.ResidueField K).injective,
        ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
    let t : Sp K ⟶ Sp Γ(S, U) := spMap (algebraMap Γ(S, U) K)
    have hi := h K (t ≫ j)
    have : IsIso (pullback.snd f' (pullback.fst s t)) := by
      have H := (IsPullback.of_hasPullback f' (pullback.fst s t)).flip.paste_vert HY.flip
      have H₀ := (IsPullback.of_hasPullback f (pullback.fst p (t ≫ j))).flip
      have hu : (pullback.fst s t ≫ gX) ≫ p = pullback.snd s t ≫ t ≫ j := by
        rw [Category.assoc, HX.w, pullback.condition_assoc]
      have e : pullback.lift _ _ hu ≫ pullback.fst p (t ≫ j) = pullback.fst s t ≫ gX := pullback.lift_fst _ _ _
      have H₁ := IsPullback.of_bot' (h₁₁ := pullback.snd f' (pullback.fst s t)) (v₁₂ := pullback.lift _ _ hu)
        (by rw [e]; exact H) H₀
      exact (MorphismProperty.isomorphisms Scheme.{0}).of_isPullback H₁.flip hi
    have h := near_isIso_of_isProper_of_finitePresentation s f' K y' hK
    have h' := Near.of_pullback f HY.flip h
    rwa [hy'] at h'
  have h := isIso_of_near f (𝟙 _) (fun y => by simpa using hn y)
  have e : f = inv (pullback.fst f (𝟙 X)) ≫ pullback.snd f (𝟙 X) := by
    rw [IsIso.eq_inv_comp, pullback.condition, Category.comp_id]
  rw [e]
  infer_instance

end Fibre

variable {S : Scheme.{0}} {A B D : Over S} [GrpObj A] [GrpObj B] [GrpObj D]

theorem isIso_of_isIso_pullback (hB : IsAbelianScheme B) (hD : IsAbelianScheme D) (x : B ⟶ D)
    (h : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso ((Over.pullback t).map x)) : IsIso x := by
  have := hB.proper
  have := hB.smooth
  have := hD.proper
  have := hD.smooth
  have : IsProper (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left D.hom
  have : Flat (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFinitePresentation (x.left ≫ D.hom) := by rw [Over.w]; infer_instance
  have : IsIso x.left := isIso_of_geometric_fibres D.hom x.left fun Ω _ _ t ↦ by
    have := h Ω t
    have hi : IsIso ((Over.pullback t).map x).left :=
      (Over.forget _).map_isIso ((Over.pullback t).map x)
    have H : IsPullback (pullback.fst B.hom t) ((Over.pullback t).map x).left x.left (pullback.fst D.hom t) := by
      refine IsPullback.of_bot (h₃₁ := t) (v₂₁ := pullback.snd D.hom t) (v₂₂ := D.hom) ?_ ?_
        (IsPullback.of_hasPullback D.hom t)
      · have e : ((Over.pullback t).map x).left ≫ pullback.snd D.hom t = pullback.snd B.hom t :=
          Over.w ((Over.pullback t).map x)
        rw [e, Over.w]
        exact IsPullback.of_hasPullback B.hom t
      · exact (pullback.lift_fst _ _ _).symm
    rw [← H.isoPullback_inv_snd]
    infer_instance
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

theorem additive_of_cube (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    {P : LB (A ⊗ B).left} (hP : P.IsLB) (h₁ : Triv (ev P (1 : B ⟶ A) (𝟙 B)))
    (h₂ : Triv (ev P (𝟙 A) (1 : A ⟶ B))) : IsAdditive P ∧ IsAdditive (swap P) := by
  have key : ∀ (T : Over S) (a b c : T ⟶ A ⊗ B),
      evc hP ((a * b * c) ≫ fst A B) ((a * b * c) ≫ snd A B) - evc hP ((a * b) ≫ fst A B) ((a * b) ≫ snd A B) -
        evc hP ((a * c) ≫ fst A B) ((a * c) ≫ snd A B) - evc hP ((b * c) ≫ fst A B) ((b * c) ≫ snd A B) +
        evc hP (a ≫ fst A B) (a ≫ snd A B) + evc hP (b ≫ fst A B) (b ≫ snd A B) +
        evc hP (c ≫ fst A B) (c ≫ snd A B) - evc hP ((1 : T ⟶ A ⊗ B) ≫ fst A B) ((1 : T ⟶ A ⊗ B) ≫ snd A B) = 0 := by
    intro T a b c
    have h := hC S (A ⊗ B) (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) P hP T a b c
    have hl := LB.isLB_linComb hP (fun k : Fin 8 ↦ (![a * b * c, a * b, a * c, b * c, a, b, c, 1] k).left)
      ![1, -1, -1, -1, 1, 1, 1, -1]
    have e := (cls_eq_zero_iff hl).2 h
    rw [cls_linComb hP _ _ hl, Fin.sum_univ_eight] at e
    simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at e
    simp only [evc, lift_comp_fst_snd]
    rw [← e]
    abel
  refine ⟨(isAdditive_iff hP).2 fun Y a a' t ↦ ?_, (BirigidLift.isAdditive_swap_iff hP).2 fun Y a t t' ↦ ?_⟩
  · have e := key Y (lift a 1) (lift a' 1) (lift 1 t)
    simp only [MonObj.mul_comp, MonObj.one_comp, lift_fst, lift_snd, _root_.mul_one, _root_.one_mul,
      evc_one_left hP h₁, evc_one_right hP h₂] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := key Y (lift 1 t) (lift 1 t') (lift a 1)
    simp only [MonObj.mul_comp, MonObj.one_comp, lift_fst, lift_snd, _root_.mul_one, _root_.one_mul,
      evc_one_left hP h₁, evc_one_right hP h₂] at e
    rw [← sub_eq_zero, ← e]
    abel

theorem IsDual.isIso_of_cls {P : LB (A ⊗ B).left} {Q : LB (A ⊗ D).left} (hP : IsDual A B P) (hQ : IsDual A D Q)
    {x : B ⟶ D} (e : cls P hP.isLB = evc hQ.isLB (fst A B) (snd A B ≫ x)) : IsIso x := by
  obtain ⟨y, hy, -⟩ := hP.univ D Q hQ.isLB hQ.additive
  have e' : cls Q hQ.isLB = evc hP.isLB (fst A D) (snd A D ≫ y) := (cls_eq_iff hQ.isLB (pull_isLB hP.isLB _)).2 hy
  refine ⟨y, BirigidLift.dual_ext hP ?_, BirigidLift.dual_ext hQ ?_⟩
  · rw [← Category.assoc, ← BirigidLift.evc_of_cls hP.isLB hQ.isLB e', ← BirigidLift.evc_of_cls hQ.isLB hP.isLB e,
      Category.comp_id]
  · rw [← Category.assoc, ← BirigidLift.evc_of_cls hQ.isLB hP.isLB e, ← BirigidLift.evc_of_cls hP.isLB hQ.isLB e',
      Category.comp_id]

theorem principalPol_selfDual : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem →
    ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
      ∀ c : GlobalTheory.CechPic.Pic (A ⊗ A).left, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c →
        ∃ (P : LB (A ⊗ A).left) (hP : P.IsLB), GlobalTheory.CechPic.cls P hP = c ∧ GlobalTheory.AbDual.IsDual A A P := by
  intro hD hC S A _ hA c hc
  obtain ⟨P, hP, rfl⟩ := cls_surj c
  refine ⟨P, hP, rfl, ?_⟩
  obtain ⟨a₁, a₂⟩ := additive_of_cube hC hA hA hP ((triv_ev_iff hP _ _).2 hc.1) ((triv_ev_iff hP _ _).2 hc.2.1)
  obtain ⟨D, _, Q, hD', -, q, q'⟩ := hD S A hA
  obtain ⟨x, hx, e⟩ := BirigidLift.exists_hom q q'.additive hP a₁ a₂
  have ix : IsIso x := isIso_of_isIso_pullback hA hD' x fun Ω _ _ s ↦ by
    obtain ⟨L, hL, -, hK, hc'⟩ := hc.2.2 Ω s
    have f := isGrpPullback_pullback A s
    have d := isGrpPullback_pullback D s
    have hA₀ := PolPull.isAbelianScheme_of_isGrpPullback hA f
    have := hA₀.comm
    obtain ⟨g, hg⟩ := AbelianDim.exists_relDim Ω _ hA₀
    have p₀ := PerfectDual.isDual_of_isPerfect hD _ _ hA₀ hA₀ hg hg (isPerfect_lam hL hK)
    obtain ⟨m, m₁, m₂⟩ := exists_prod_pullback f d
    have hQ := pull_isLB q.isLB m
    have q₀ := q.baseChange f d m₁ m₂ hQ ((cls_eq_iff hQ hQ).1 rfl)
    refine p₀.isIso_of_cls q₀ ?_
    have l₁ : IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ (fst A A).left = (fst _ _ : _ ⟶ (Over.pullback s).obj A).left ≫
        pullback.fst A.hom s :=
      congrArg (fun z ↦ z.left) (lift_fst (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))
    have l₂ : IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s ≫ (snd A A).left = (snd _ _ : _ ⟶ (Over.pullback s).obj A).left ≫
        pullback.fst A.hom s :=
      congrArg (fun z ↦ z.left) (lift_snd (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (fst _ _)) (IndefiniteRowSideFullHecke.ZeroSectionBase.toBase A s (snd _ _)))
    rw [← BirigidLift.pull_evc_eq l₁ l₂ m₁ m₂ q.isLB hQ (x := x) (pullback.lift_fst _ _ _).symm, ← e, hc']
    exact cls_cube_two hL _ _ _
  exact isDual_of_iso S A A D P Q q hP x ix hx ((cls_eq_iff hP (pull_isLB q.isLB _)).1 e)

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefPullbackIsNef
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NumPull

theorem isNef_pull_of_isProjOver : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (s : Y ⟶ X), IsProjOver p → ∀ N : LB X, (letI := algebraΓOfHom p; IsNef k N) → (letI := algebraΓOfHom (s ≫ p); IsNef k (N.pull s)) := by
  intro k _ X Y p s hp N hN
  letI := algebraΓOfHom p
  letI := algebraΓOfHom (s ≫ p)
  have : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  refine ⟨pull_isLB hN.isLB s, fun C hC => ?_⟩
  rcases interNumRed_pull_curve p s C hC with h | ⟨C', hC', d, hd⟩
  · rw [h N hN.isLB]
  · rw [hd N hN.isLB]
    exact mul_nonneg (Int.natCast_nonneg d) (hN.nonneg C' hC')

end GlobalTheory.NumPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame KSIso)

theorem isUnit_ger_of_ev {Z : Scheme.{0}} {V : Z.Opens} (a : Γ(Z, V)) (y : Z) (hy : y ∈ V)
    (h : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), GlobalTheory.FlagMod.ev z V hz a ≠ 0) :
    IsUnit (ger y hy a) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
  have hWV : W ≤ V := hWV
  replace hW : IsAffineOpen W := hW
  let p := hW.primeIdealOf ⟨y, hyW⟩
  have hne := h p.asIdeal.ResidueField (spMap (algebraMap Γ(Z, W) p.asIdeal.ResidueField) ≫ GlobalTheory.FlagMod.tau hW)
    (GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le hW hWV))
  rw [← GlobalTheory.FlagMod.ev_res _ hWV (GlobalTheory.FlagMod.le_preimage_comp _ (GlobalTheory.FlagMod.tau_le hW le_rfl)),
    GlobalTheory.FlagMod.ev_spMap_tau] at hne
  have hnm : resG Z hWV a ∈ p.asIdeal.primeCompl := fun hm => hne (Ideal.algebraMap_residueField_eq_zero.2 hm)
  letI := Z.presheaf.algebra_section_stalk (⟨y, hyW⟩ : W)
  have := hW.isLocalization_stalk ⟨y, hyW⟩
  have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (Z.presheaf.stalk y) p.asIdeal (resG Z hWV a)).2 hnm
  rw [← ger_resG hWV y hyW]
  exact hu

theorem canId_nonempty : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F))
    (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)),
    (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) →
    Nonempty (CanId M) := by
  intro hdR E _ _ _ H Dw l Xo c Y X Z M hKS
  haveI : Smooth M.str := SmoothOfRelativeDimension.smooth (dimFlag Dw) M.str
  haveI : IsReduced M.X := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isReduced_of_smooth M.str
  have hBLB : (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).IsLB :=
    LB.isLB_div M.K.isLB (LB.isLB_pull ((common₀ X Z).isLB _) M.σ)
  have hloc : ∀ t : M.K.bundle.ι × X.F.J, ∃ a : Γ(M.X, ksOpen M t.1 t.2), ∀ (K : Type) [Field K]
      (z : Sp K ⟶ M.X) (hz : ⊤ ≤ z ⁻¹ᵁ ksOpen M t.1 t.2), KSRel M t.1 t.2 z (GlobalTheory.FlagMod.ev z _ hz a) := fun t =>
    GlobalTheory.FlagMod.glue_field (ksOpen M t.1 t.2) (fun L _ z x => KSRel M t.1 t.2 z x)
      (fun L _ z hz x y hx hy => (_root_.GlobalTheory.CompHS.ksRel_unique_ne_zero M hKS t.1 t.2 L z hz).1 x y hx hy)
      (fun W hW hle => _root_.GlobalTheory.CompHS.exists_regular_ksRel M hdR hKS t.1 t.2 W hW hle)
  choose a ha using hloc
  have cover : ∀ y ∈ M.off, ∃ t : M.K.bundle.ι × X.F.J, y ∈ ksOpen M t.1 t.2 := by
    intro y hy
    obtain ⟨i, hi⟩ := exists_chart M.K.isLB y
    obtain ⟨k, hk⟩ := ((common₀ X Z).pull M.σ).cover y
    exact ⟨(i, k), hy, hi, (((common₀ X Z).pull M.σ).mem _ k y).2 hk⟩
  have rule : ∀ (y : M.X) (t t' : M.K.bundle.ι × X.F.J) (h : y ∈ ksOpen M t.1 t.2) (h' : y ∈ ksOpen M t'.1 t'.2),
      ger y h (a t) = (tr (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) y (t.1, flagIdx M _ t.2)
        (t'.1, flagIdx M _ t'.2) : _) * ger y h' (a t') := by
    intro y t t' h h'
    have hle : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤
        (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (t.1, flagIdx M _ t.2) ⊓
          (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (t'.1, flagIdx M _ t'.2) :=
      fun q hq => ⟨hq.1.2, hq.2.2⟩
    rw [val_tr _ y (hle ⟨h, h'⟩)]
    have e : resG M.X (inf_le_left : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) (a t) =
        resG M.X hle ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (t.1, flagIdx M _ t.2)
          (t'.1, flagIdx M _ t'.2)).val * resG M.X inf_le_right (a t') := by
      refine GlobalTheory.FlagMod.ext_ev_field fun L _ z hz => ?_
      have h1 := GlobalTheory.FlagMod.le_preimage_mono inf_le_left hz
      have h2 := GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz
      have hg := GlobalTheory.FlagMod.le_preimage_mono hle hz
      rw [map_mul, GlobalTheory.FlagMod.ev_res z _ hz h1, GlobalTheory.FlagMod.ev_res z _ hz h2, GlobalTheory.FlagMod.ev_res z _ hz hg]
      exact _root_.GlobalTheory.CompHS.ksRel_change M hKS t.1 t'.1 t.2 t'.2 L z h1 h2 hg _ _ (ha t L z h1) (ha t' L z h2)
    have := congrArg (ger y (⟨h, h'⟩ : y ∈ ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2)) e
    have e1 := ger_resG (inf_le_left : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) y ⟨h, h'⟩ (a t)
    have e2 := ger_resG (inf_le_right : ksOpen M t.1 t.2 ⊓ ksOpen M t'.1 t'.2 ≤ _) y ⟨h, h'⟩ (a t')
    have e3 := ger_resG hle y ⟨h, h'⟩ ((LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).g (t.1, flagIdx M _ t.2)
          (t'.1, flagIdx M _ t'.2)).val
    rw [map_mul, e1, e2, e3] at this
    exact this
  obtain ⟨f, hf⟩ := H0.exists_of_germs (p := M.str) (O := M.off) hBLB
    (fun t : M.K.bundle.ι × X.F.J => ksOpen M t.1 t.2) (fun t => (t.1, flagIdx M _ t.2))
    (fun t => inf_le_left) (fun t => inf_le_right) cover a rule
  have hloc' : ∀ i k, f.loc (i, flagIdx M _ k) = a (i, k) := fun i k =>
    fun_ext_ger fun y hy => (H0.germ_apply _ y hy.1 hy.2 f).symm.trans (hf (i, k) y hy)
  refine ⟨⟨f, nowhereZero_of_exists fun y hy => ?_, (isKS_iff_ksRel M f).2 @fun K _ z i k ho hi => ?_⟩⟩
  · obtain ⟨t, ht⟩ := cover y hy
    refine ⟨(t.1, flagIdx M _ t.2), ht.2, ?_⟩
    rw [hf t y ht]
    exact isUnit_ger_of_ev (a t) y ht fun L _ z hz => (_root_.GlobalTheory.CompHS.ksRel_unique_ne_zero M hKS t.1 t.2 L z hz).2 _ (ha t L z hz)
  · have hk : KSRel M i k z (GlobalTheory.FlagMod.ev z (ksOpen M i k) (GlobalTheory.FlagMod.le_preimage_inf ho hi) (a (i, k))) :=
      ha (i, k) K z (GlobalTheory.FlagMod.le_preimage_inf ho hi)
    have e : H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi f =
        GlobalTheory.FlagMod.ev z (ksOpen M i k) (GlobalTheory.FlagMod.le_preimage_inf ho hi) (a (i, k)) := by
      rw [← hloc' i k]
      rfl
    rw [e]
    exact @hk

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImage
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheaf

theorem normDescentSheaf : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z), IsFinite π → IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) →
    CharZero Γ(Y, ⊤) → ∀ I : Y.IdealSheafData, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ ξ : Sp V ⟶ Z, ξ (closedPoint V) ∈ Set.range π →
        ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
          (f : V →+* V') (ψ : Fin d → (Sp V' ⟶ Y)), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧
          IsLocalHom f ∧ (∀ j, ψ j ≫ π = spMap f ≫ ξ) ∧ (idlAlong J ξ).map f = ∏ j, idlAlong I (ψ j) := by
  intro Y Z π hπ hY hYn hYN hZN hopen hchar I
  haveI : IsAffineHom π := hπ.toIsAffineHom
  obtain ⟨K, L, _, _, _, _, hK, J, hsupp, hJ⟩ := _root_.GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists Y Z π hY hYn hYN hZN hopen hchar I
  refine ⟨Module.finrank K L, J, Module.finrank_pos, hsupp, ?_⟩
  intro V _ _ _ _ hV ξ hξ
  obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens
    (show ξ (closedPoint V) ∈ (⟨Set.range π, hopen⟩ : Z.Opens) from hξ)
  have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hxU).ge
  let U' : Z.affineOpens := ⟨U, hU⟩
  obtain ⟨_, _, hA, hAc, hB, hfin, hKf, hLf, hsq, hJU⟩ := hJ U' hUW ⟨_, hxU⟩
  obtain ⟨V', _, _, _, _, f, ψ', hV', hf, hfl, hψc, hprod⟩ := _root_.GlobalTheory.NormSheaf.normIdeal_map_eq_prod_lifts Γ(Z, U') Γ(Y, π ⁻¹ᵁ U) K L (π.app U).hom
    hfin hsq (I.ideal ⟨π ⁻¹ᵁ U, U'.2.preimage π⟩) V hV (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (.of V)).hom).hom
  choose ψ hψ hψI using fun j => _root_.GlobalTheory.AffinePointLift.exists_lift Y Z π U' V V' ξ hle f (ψ' j) (hψc j)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f, ψ, hV', hf, hfl, hψ, ?_⟩
  have hidl : idlAlong J ξ = (J.ideal U').map
      (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (.of V)).hom).hom := by
    have hx : ξ (closedPoint V) ∈ U := hle trivial
    unfold idlAlong
    rw [ReciprocityTheory.AnForm.R.ds_stalkId_eq_map J U' _ hx, Ideal.map_map, ← CommRingCat.hom_comp,
      Scheme.germ_stalkClosedPointTo]
    congr 2
  rw [hidl, hJU, Ideal.map_map]
  simp only [hψI]
  exact hprod

end GlobalTheory.NormSheaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorialInvLe
section
noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD)

namespace GlobalTheory.JetExp

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_mul {r r' : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r' y) : Sz l lam (r + r') (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have e : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [e, map_mul, norm_mul, Real.rpow_add hl]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (h : r ≤ r') (hx : Sz l lam r x) : Sz l lam r' x :=
  ⟨hx.1, hx.2.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) h)⟩

theorem sz_one : Sz l lam 0 1 := ⟨one_mem _, by
  have e : (⟨1, one_mem _⟩ : algebraicClosure ℚ ℂ) = 1 := rfl
  rw [e, map_one, norm_one, Real.rpow_zero]⟩

theorem sz_prod {ι : Type} (t : Finset ι) (r : ι → ℝ) (f : ι → ℂ) (h : ∀ i ∈ t, Sz l lam (r i) (f i)) :
    Sz l lam (∑ i ∈ t, r i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (sz_one (l := l) (lam := lam))
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact sz_mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem norm_factorial_inv_le (n : ℕ) : ‖((n.factorial : ℂ_[l]))‖⁻¹ ≤ (l : ℝ) ^ (n : ℝ) := by
  have hp : l.Prime := Fact.out
  have e1 : ((n.factorial : ℂ_[l])) = (((n.factorial : ℚ) : ℚ_[l]) : ℂ_[l]) := by simp
  rw [e1, PadicComplex.norm_extends', Padic.eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero (by exact_mod_cast Nat.factorial_ne_zero n), padicValRat.of_nat]
  have hv : multiplicity l n.factorial ≤ n := multiplicity_factorial_le l n
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hp.one_lt.le
  rw [Rat.cast_zpow, Rat.cast_natCast, zpow_neg, inv_inv, zpow_natCast, Real.rpow_natCast]
  exact pow_le_pow_right₀ hl1 hv

theorem sz_factorial_inv (n : ℕ) : Sz l lam (n : ℝ) ((n.factorial : ℂ)⁻¹) := by
  have hm : ((n.factorial : ℂ)⁻¹) ∈ algebraicClosure ℚ ℂ := inv_mem (natCast_mem _ _)
  refine ⟨hm, ?_⟩
  have e : (⟨(n.factorial : ℂ)⁻¹, hm⟩ : algebraicClosure ℚ ℂ) = ((n.factorial : algebraicClosure ℚ ℂ))⁻¹ := by
    ext; simp
  rw [e, map_inv₀, map_natCast, norm_inv]
  exact norm_factorial_inv_le n

theorem expansion_of_jetInt : JetInt → Expansion := by
  classical
  intro hJ E _ _ _ _ I _ d φ s hφ hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ _ lam Ω hΩ
  obtain ⟨a, b, hab, hX⟩ := hJ E I d φ s hφ hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy lam Ω hΩ
  refine ⟨a, b, hab, fun g κ u hg hu => ?_⟩
  have h1 := hX g κ u hg hu
  have h2 : Sz l lam ((∑ i, κ i : ℕ) : ℝ) (∏ i, ((κ i).factorial : ℂ)⁻¹) := by
    rw [Nat.cast_sum]
    exact sz_prod _ _ _ fun i _ => sz_factorial_inv (κ i)
  have e : iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))) =
      (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s))) * ∏ i, ((κ i).factorial : ℂ)⁻¹ := by
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_mul_eq_div_div, div_eq_mul_inv (_ / _)]
  rw [e]
  refine sz_mono ?_ (sz_mul h1 h2)
  have hK : (0 : ℝ) ≤ ((∑ i, κ i : ℕ) : ℝ) := Nat.cast_nonneg _
  split_ifs <;> nlinarith

end GlobalTheory.JetExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectPairingTorsionModule
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_pairing_torsion_module : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e) → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.F) M] [Finite M], (∀ x : M, c • x = 0) → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (e : M → M → kˣ), (∀ x x' y, e (x + x') y = e x y * e x' y) → (∀ x y y', e x (y + y') = e x y * e x y') → (∀ (a : 𝓞 D.F) x y, e (a • x) y = e x (D.bar a • y)) → (∀ x y, e x y * e y x = 1) → (∀ x, (∀ y, e x y = 1) → x = 0) → Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} → ∃ H : Submodule (𝓞 D.F) M, (∀ x ∈ H, ∀ y ∈ H, e x y = 1) ∧ (∀ x, (∀ y ∈ H, e x y = 1) → x ∈ H) ∧ (∀ x ∈ H, (∃ i : ℕ, ∀ a ∈ uIdeal D r ^ i, a • x = 0) → ∀ a ∈ w, a • x = 0) ∧ Nat.card {x : M // x ∈ H ∧ ∀ a ∈ w, a • x = 0} = Ideal.absNorm w ^ j := by
  first | (exact @GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (exact GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (intros; apply GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type  <;> assumption)
end

