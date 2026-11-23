module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1095
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharLineBundleFibreModpEqRatProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

noncomputable section

namespace GlobalTheory.ChiFibre

open GlobalTheory.AbLaw GlobalTheory.Adelic GlobalTheory.FieldChangeInter

theorem alternating_sum_range_telescoping_identity (a r : ℕ → ℤ) (m : ℕ) :
    ∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * (a n + a (n + 1) - r (n + 1)) =
      ∑ n ∈ Finset.range m, (-1 : ℤ) ^ n * r n + (a 0 - r 0) + (-1) ^ m * (r m - a m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
    ring

theorem homology_subsingleton {R : Type} [Ring R] (K : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (h : IsZero (K.X n)) : Subsingleton (K.homology n) :=
  ModuleCat.subsingleton_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) h)

theorem finite_int_congr {M : Type*} [AddCommGroup M] {i₁ i₂ : Module ℤ M}
    (h : @Module.Finite ℤ M _ _ i₁) : @Module.Finite ℤ M _ _ i₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  exact h

theorem altSum (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime]
    (hinj : ∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0)
    (hfin : ∀ n, Module.Finite ℤ (C.homology n)) (m : ℕ) (hz : ∀ n, m ≤ n → IsZero (C.X n)) :
    ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank (ZMod p) ((((ModuleCat.extendScalars
      (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
    ∑ᶠ n, (-1 : ℤ) ^ n * (Module.finrank ℚ ((((ModuleCat.extendScalars
      (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) := by
  set a : ℕ → ℤ := fun n => Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology n))
  set r : ℕ → ℤ := fun n => Module.finrank ℤ (C.homology n)
  have hsub : ∀ n, m ≤ n → Subsingleton (C.homology n) :=
    fun n hn => homology_subsingleton C n (hz n hn)
  have hr0 : ∀ n, m ≤ n → r n = 0 := fun n hn => by
    haveI := hsub n hn
    simp only [r]
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  have ha0 : ∀ n, m ≤ n → a n = 0 := fun n hn => by
    haveI := hsub n hn
    have : Subsingleton (TensorProduct ℤ (ZMod p) (C.homology n)) := inferInstance
    simp only [a]
    rw [Module.finrank_zero_of_subsingleton]
    rfl
  have hext : ∀ (F : Type) [Field F] (g : ℤ →+* F) (n : ℕ), m ≤ n →
      Module.finrank F ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).homology n) = 0 := by
    intro F _ g n hn
    have hZ : IsZero ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj C).X n) :=
      (ModuleCat.extendScalars g).map_isZero (hz n hn)
    haveI := homology_subsingleton _ n hZ
    exact Module.finrank_zero_of_subsingleton
  have hsupp : ∀ (F : Type) [Field F] (g : ℤ →+* F),
      (Function.support fun n => (-1 : ℤ) ^ n * (Module.finrank F ((((ModuleCat.extendScalars
        g).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ)) ⊆
        ↑(Finset.range m) := by
    intro F _ g n hn
    by_contra h
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
    exact hn (by simp [hext F g n h])
  rw [finsum_eq_sum_of_support_subset _ (hsupp (ZMod p) _),
    finsum_eq_sum_of_support_subset _ (hsupp ℚ _)]
  have h1 : ∀ n ∈ Finset.range m, (-1 : ℤ) ^ n * (Module.finrank (ZMod p) ((((ModuleCat.extendScalars
      (Int.castRingHom (ZMod p))).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
      (-1 : ℤ) ^ n * (a n + a (n + 1) - r (n + 1)) := fun n _ => by
    rw [_root_.GlobalTheory.uct_mod_p C p hinj hfin n]
  have h2 : ∀ n ∈ Finset.range m, (-1 : ℤ) ^ n * (Module.finrank ℚ ((((ModuleCat.extendScalars
      (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) : ℤ) =
      (-1 : ℤ) ^ n * r n := fun n _ => by
    rw [GlobalTheory.T.finrank_rat_homology_eq_finrank_int C n (hfin n)]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, alternating_sum_range_telescoping_identity]
  have h0 : a 0 = r 0 := by
    simp only [a, r]
    exact_mod_cast _root_.GlobalTheory.finrank_zmod_tensor_homology_zero C p (hinj 0) (hfin 0)
  rw [h0, hr0 m le_rfl, ha0 m le_rfl]
  ring

theorem hdim_fibre {X X' : Scheme.{0}} {F : Type} [Field F] (g : ℤ →+* F) (f : X ⟶ Sp ℤ)
    (f' : X' ⟶ Sp F) (π : X' ⟶ X) (H : IsPullback π f' f (spMap g)) {κ : Type} [LinearOrder κ]
    [Finite κ] (D : κ → X.Opens) (hc : ⨆ i, D i = ⊤)
    (hD : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, D i)) (M : LB X) (hM : M.IsLB)
    (n : ℕ) :
    (letI := GlobalTheory.algebraΓOfHom f'; hdim F (toMod (M.pull π)) n) =
      Module.finrank F ((((ModuleCat.extendScalars g).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (cechLB f M D)).homology n) := by
  letI := GlobalTheory.algebraΓOfHom f'
  have hM' := LB.isLB_pull hM π
  haveI := LB.isQuasicoherent_toMod hM'
  have hc' : ⨆ i, π ⁻¹ᵁ D i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, hc]; rfl
  have hD' : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (⨅ i ∈ s, π ⁻¹ᵁ D i) :=
    fun s hs => isAffineOpen_biInf_preimage H (hD s hs)
  have e₁ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (cechIso f' (M.pull π) (fun i => π ⁻¹ᵁ D i))).toLinearEquiv ≪≫ₗ
    cechHEquivCoh F hc' hD' (toMod (M.pull π)) n
  have e₄ := ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (cechLBBaseChangeIso hM H hD)).toLinearEquiv
  rw [hdim_def, ← e₁.finrank_eq, ← e₄.finrank_eq]
  rfl

theorem chi_fibres_LB {X Xp Xq : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (hX : CharZero Γ(X, ⊤))
    (f : X ⟶ Sp ℤ) (p : ℕ) [Fact p.Prime]
    (fp : Xp ⟶ Sp (ZMod p)) (πp : Xp ⟶ X) (Hp : IsPullback πp fp f (spMap (Int.castRingHom (ZMod p))))
    (fq : Xq ⟶ Sp ℚ) (πq : Xq ⟶ X) (Hq : IsPullback πq fq f (spMap (Int.castRingHom ℚ)))
    (M : LB X) (hM : M.IsLB)
    (hfin : ∀ n, letI := GlobalTheory.algebraΓOfHom f; Module.Finite ℤ (coh (twist (structureModule X) M) n)) :
    (letI := GlobalTheory.algebraΓOfHom fp; chi (ZMod p) (toMod (M.pull πp))) =
      (letI := GlobalTheory.algebraΓOfHom fq; chi ℚ (toMod (M.pull πq))) := by
  obtain ⟨m, Dc, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  have hinj : ∀ (n : ℕ) (x : (cechLB f M Dc).X n), (p : ℤ) • x = 0 → x = 0 :=
    fun n x => _root_.GlobalTheory.CechPic.cechLB_X_noZSMulDivisors hX f M Dc n (p : ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero) x
  have hz : ∀ n, m ≤ n → IsZero ((cechLB f M Dc).X n) :=
    fun n hn => isZero_cechLB_X f M Dc (by simpa using hn)
  have hfin' : ∀ n, Module.Finite ℤ ((cechLB f M Dc).homology n) := by
    intro n
    letI := GlobalTheory.algebraΓOfHom f
    obtain ⟨e⟩ := nonempty_coh_equiv f hM hc hD' n
    letI : Module ℤ (coh (twist (structureModule X) M) n) := cohOn.instModule ℤ _ ⊤ n
    haveI hf1 : Module.Finite ℤ (coh (twist (structureModule X) M) n) := finite_int_congr (hfin n)
    exact finite_int_congr (Module.Finite.equiv e.symm)
  letI := GlobalTheory.algebraΓOfHom fp
  letI := GlobalTheory.algebraΓOfHom fq
  rw [chi_def, chi_def]
  have hp := fun n => hdim_fibre (Int.castRingHom (ZMod p)) f fp πp Hp Dc hc hD' M hM n
  have hq := fun n => hdim_fibre (Int.castRingHom ℚ) f fq πq Hq Dc hc hD' M hM n
  simp only [hp, hq]
  exact altSum (cechLB f M Dc) p hinj hfin' m hz

theorem chi_structureModule_eq {X X' : Scheme.{0}} (F : Type) [Field F] [Algebra F Γ(X', ⊤)]
    (π : X' ⟶ X) : chi F (structureModule X') = chi F (toMod ((LB.triv X).pull π)) := by
  have h₀ := LB.isLB_triv X
  have h₁ := Semi.LB.isLB_pull h₀ π
  obtain ⟨e'⟩ := nonempty_twist_iso_of_cls_eq_zero (structureModule X') h₁
    ((CechPic.cls_pull h₀ π h₁).trans (map_zero _))
  rw [← chi_congr F e', chi_congr F (Twist.unitTwistIso _)]

theorem chi_fibre_eq : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (D : ℕ), IsArithVar q D → ∀ (p : ℕ) [Fact p.Prime] (N : LB W), N.IsLB → (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); chi (ZMod p) (toMod (N.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) = chi ℚ (toMod (N.pull (ratFibre.fst q))) ∧ chi (ZMod p) (structureModule (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))) = chi ℚ (structureModule (ratFibre q))) := by
  intro k _ W q D hq p _ N hN
  haveI := hq.isDomain
  haveI := hq.finite
  haveI := hq.isIntegral
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hproj := hq.isProjOver
  haveI : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hproj).1
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace q
  haveI := isAffineHom_diagonal_of_isSeparated q
  have hX : CharZero Γ(W, ⊤) := (flat_int_iff_charZero _).1 hq.flat
  have hfin : ∀ M : LB W, M.IsLB → ∀ n,
      letI := GlobalTheory.algebraΓOfHom (q ≫ spMap (Int.castRingHom k))
      Module.Finite ℤ (coh (twist (structureModule W) M) n) := by
    intro M hM n
    letI := GlobalTheory.algebraΓOfHom q
    have h1 : Module.Finite k (coh (twist (structureModule W) M) n) :=
      (((serre_finiteness_vanishing k W (structureModule W)).2 q (fun _ => rfl)).2
        (Or.inl hproj)).2.1 M hM n
    have h2 : Module.Finite ℤ (coh (twist (structureModule W) M) n) := Module.Finite.trans k _
    exact finite_int_congr h2
  refine ⟨chi_fibres_LB hX _ p _ _ (IsPullback.of_hasPullback _ _) _ _ (ratFibre.isPullback q) N hN
    (hfin N hN), ?_⟩
  letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k))
    (spMap (Int.castRingHom (ZMod p))))
  rw [chi_structureModule_eq (ZMod p) (pullback.fst _ _), chi_structureModule_eq ℚ (ratFibre.fst q)]
  exact chi_fibres_LB hX _ p _ _ (IsPullback.of_hasPullback _ _) _ _ (ratFibre.isPullback q) _
    (LB.isLB_triv W) (hfin _ (LB.isLB_triv W))

end GlobalTheory.ChiFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvRFrMapOfIsReduced
section
noncomputable section

namespace GlobalTheory.FlagMod

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem eq_of_field_maps {S : Type} [CommRing S] [_root_.IsReduced S] {a b : S}
    (h : ∀ (L : Type) [Field L] (ψ : S →+* L), ψ a = ψ b) : a = b := by
  rw [← sub_eq_zero]
  refine IsNilpotent.eq_zero (mem_nilradical.1 ?_)
  rw [nilradical_eq_sInf, Ideal.mem_sInf]
  intro p hp
  haveI : p.IsPrime := hp
  rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, h _ (algebraMap S p.ResidueField), sub_self]

theorem eq_of_field_algHoms {K S : Type} [CommRing K] [CommRing S] [Algebra K S] [_root_.IsReduced S] {a b : S}
    (h : ∀ (L : Type) [Field L] [Algebra K L] (ψ : S →ₐ[K] L), ψ a = ψ b) : a = b :=
  eq_of_field_maps fun L _ ψ =>
    letI : Algebra K L := (ψ.comp (algebraMap K S)).toAlgebra
    h L { ψ with commutes' := fun _ => rfl }

theorem ext_ev_field {Z : Scheme.{0}} [IsReduced Z] {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), ev z V hz a = ev z V hz b) : a = b := by
  apply TopCat.Presheaf.section_ext Z.sheaf V
  intro p hp
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp V.isOpen
  have hWV : W ≤ V := hWV
  have e0 : ev (tau hW) V (tau_le hW hWV) a = ev (tau hW) V (tau_le hW hWV) b :=
    eq_of_field_maps fun L _ ψ => by
      have := h L (spMap ψ ≫ tau hW) (le_preimage_comp _ (tau_le hW hWV))
      rwa [ev_spMap ψ _ V (tau_le hW hWV)] at this
  rw [ev_tau hW hWV, ev_tau hW hWV] at e0
  have e1 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW a
  have e2 := Z.presheaf.germ_res_apply (homOfLE hWV) p hpW b
  exact e1.symm.trans ((congrArg _ e0).trans e2)

theorem glue_field {Z : Scheme.{0}} [IsReduced Z] (V : Z.Opens)
    (R : ∀ (L : Type) [Field L], (Sp L ⟶ Z) → L → Prop)
    (uniq : ∀ (L : Type) [Field L] (z : Sp L ⟶ Z), ⊤ ≤ z ⁻¹ᵁ V → ∀ x y, R L z x → R L z y → x = y)
    (loc : ∀ W : Z.Opens, IsAffineOpen W → W ≤ V → ∃ a : Γ(Z, W),
      ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ W), R L z (ev z W hz a)) :
    ∃ a : Γ(Z, V), ∀ (L : Type) [Field L] (z : Sp L ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ V), R L z (ev z V hz a) := by
  let I := {W : Z.Opens // IsAffineOpen W ∧ W ≤ V}
  choose a ha using fun i : I => loc i.1 i.2.1 i.2.2
  have hc : ∀ p ∈ V, ∃ i : I, p ∈ i.1 := fun p hp => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp V.isOpen
    exact ⟨⟨W, hW, hWV⟩, hpW⟩
  obtain ⟨s, hs, -⟩ := Z.sheaf.existsUnique_gluing' (fun i : I => i.1) V (fun i => homOfLE i.2.2)
    (fun p hp => TopologicalSpace.Opens.mem_iSup.2 (hc p hp)) a (fun i j => by
      refine ext_ev_field (a := resG Z inf_le_left (a i)) (b := resG Z inf_le_right (a j)) fun L _ z hz => ?_
      have hi := le_preimage_mono inf_le_left hz
      have hj := le_preimage_mono inf_le_right hz
      rw [ev_res z _ hz hi, ev_res z _ hz hj]
      exact uniq L z (le_preimage_mono i.2.2 hi) _ _ (ha i L z hi) (ha j L z hj))
  refine ⟨s, fun L _ z hz => ?_⟩
  obtain ⟨i, hi⟩ := hc (z (IsLocalRing.closedPoint L)) (hz (Set.mem_univ _))
  have hi' : ⊤ ≤ z ⁻¹ᵁ i.1 := ((IsLocalRing.closed_point_mem_iff (U := z ⁻¹ᵁ i.1)).1 hi).ge
  have e : ev z V hz s = ev z i.1 hi' (a i) := (ev_res z i.2.2 hi' hz s).symm.trans (congrArg _ (hs i))
  exact e ▸ ha i L z hi'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

namespace FlagCover

theorem isReduced_Yo (hi : Function.Injective β) (hs : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (X : FlagCover Y) : IsReduced X.Yo := by
  letI := β.toAlgebra
  haveI : IsDomain O := hi.isDomain β
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hi
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun x => by
    obtain ⟨a, b, hb, h⟩ := hs x
    exact ⟨a, b, (eq_div_iff hb).2 h⟩
  have h1 : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (R := O) (S := c.F) (nonZeroDivisors O)
  have h2 : Flat (spMap β) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact IsLocalization.flat c.F (nonZeroDivisors O)
  have := Y.jQ_open
  have h3 : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have h4 : Flat Y.j := by unfold Model.j; infer_instance
  have h5 : IsPreimmersion X.inc :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h3
  have : ∀ x : X.Yo, _root_.IsReduced (X.Yo.presheaf.stalk x) := fun x => by
    have := (X.normal (X.inc x)).1
    let _ := (X.inc.stalkMap x).hom.toAlgebra
    have : Module.Flat (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x) := Flat.stalkMap X.inc x
    have : IsLocalHom (algebraMap (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (X.inc.stalkMap x).hom)
    have : Module.FaithfullyFlat (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    let e := RingEquiv.ofBijective (X.inc.stalkMap x).hom
      ⟨FaithfulSMul.algebraMap_injective (X.YY.presheaf.stalk (X.inc x)) (X.Yo.presheaf.stalk x),
        X.inc.stalkMap_surjective x⟩
    exact isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_isReduced_stalk _

theorem evR_frMap_of_isReduced {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    [_root_.IsReduced S] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  obtain ⟨p, a, u, hu⟩ := (evLaws_genFr_atlas E H Dw l Xo c).1.test S y
  rw [FlagTan.evR_eq hf hu, FlagTan.evR_eq hf (PullbackSections.frMap_trans a φ hu h)]
  rfl

variable {X : FlagCover Y} {e : Ix Dw → ℤ}

theorem exists_alg_chartFr {S : Type} [CommRing S] (w : Sp S ⟶ X.Yo) :
    ∃ _ : Algebra c.F S, ∀ (k : X.F.J) (hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k),
      ∃ Q : FrPt Xo c S, X.F.ChartFr k (w ≫ X.inc) hz Q ∧ X.pt Q = w :=
  letI : Algebra c.F S :=
    ((ev (w ≫ pullback.snd X.π Y.j ≫ pullback.snd _ _) ⊤ le_top).comp (toΓ c.F)).toAlgebra
  ⟨this, fun k hz => X.exists_chartFr w (spMap_ev_top _).symm k hz⟩

theorem exists_coef [IsReduced X.Yo] {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) (k : X.F.J) :
    ∃ a : Γ(X.Yo, ((X.F.LL e).pull X.inc).U (fun _ => k)), ∀ (L : Type) [Field L] (z : Sp L ⟶ X.Yo)
      (hz' : ⊤ ≤ z ⁻¹ᵁ ((X.F.LL e).pull X.inc).U (fun _ => k)) [Algebra c.F L]
      (hz : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c L), X.F.ChartFr k (z ≫ X.inc) hz Q → X.pt Q = z →
      ev z _ hz' a = evR Xo c f Q := by
  refine glue_field _ (fun L _ z x => ∀ [Algebra c.F L] (hz : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c L),
    X.F.ChartFr k (z ≫ X.inc) hz Q → X.pt Q = z → x = evR Xo c f Q) (fun L _ z hz' x y hx hy => ?_)
    fun W hW hle => ?_
  · obtain ⟨_, h⟩ := exists_alg_chartFr z
    obtain ⟨Q, hQ, ez⟩ := h k fun p hp => mem_pull.1 (hz' hp)
    exact (hx _ Q hQ ez).trans (hy _ Q hQ ez).symm
  · obtain ⟨_, h⟩ := exists_alg_chartFr (tau hW)
    obtain ⟨Q₀, hQ₀, e₀⟩ := h k fun p hp => mem_pull.1 (tau_le hW hle hp)
    refine ⟨evR Xo c f Q₀, fun L _ z hzW _ hz Q hQ ez => ?_⟩
    have e1 : spMap (ev z W hzW) ≫ tau hW = z := spMap_ev z hW hzW
    have e2 : spMap ((ev z W hzW).comp (algebraMap c.F Γ(X.Yo, W))) = spMap (algebraMap c.F L) := by
      rw [← spMap_comp', ← frX_snd Q₀, ← frX_snd Q, ← X.pt_snd Q₀, ← X.pt_snd Q, e₀, ez]
      simp only [← Category.assoc, e1]
    have e3 : (ev z W hzW).comp (algebraMap c.F Γ(X.Yo, W)) = algebraMap c.F L :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    let φ : Γ(X.Yo, W) →ₐ[c.F] L := { ev z W hzW with commutes' := fun r => DFunLike.congr_fun e3 r }
    obtain ⟨Q', hQ'⟩ := exists_frMap φ Q₀
    have e4 : spMap φ.toRingHom ≫ tau hW ≫ X.inc = z ≫ X.inc := by
      rw [← Category.assoc]; exact congrArg (· ≫ X.inc) e1
    rw [hQ.unique (hQ₀.frMap hQ' e4 hz)]
    exact (evR_frMap_of_isReduced hf hQ').symm

theorem exists_toRule_eq [IsReduced X.Yo] {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c e) :
    ∃ s : X.SecO e, toRule s = f := by
  classical
  choose a ha using exists_coef (X := X) (e := e) hf.1
  let s : X.SecO e := ⟨fun j => a (j PUnit.unit), fun j j' => ext_ev_field fun L _ z hw => by
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j PUnit.unit, rfl⟩
    obtain ⟨k', rfl⟩ : ∃ k, j' = fun _ => k := ⟨j' PUnit.unit, rfl⟩
    have hh : ⊤ ≤ (z ≫ X.inc) ⁻¹ᵁ (X.F.U k ⊓ X.F.U k') :=
      fun p hp => ⟨(mem_pull (F := X.inc)).1 (hw hp).1, (mem_pull (F := X.inc)).1 (hw hp).2⟩
    have hz := le_preimage_mono inf_le_left hh
    have hz' := le_preimage_mono inf_le_right hh
    obtain ⟨_, h⟩ := exists_alg_chartFr z
    obtain ⟨Q, hQ, ez⟩ := h k hz
    obtain ⟨Q', hQ', ez'⟩ := h k' hz'
    have hwt := FlagTan.evR_frBor hf (hQ.frBor hQ' hh)
    rw [map_mul]
    refine (ev_res z _ hw (le_pull hz) _).trans ((ha k L z _ hz Q hQ ez).trans (Eq.trans ?_
      (congrArg₂ (· * ·) ((ev_pull_g (X.F.LL e) X.inc (fun _ => k) (fun _ => k') z hw hh).trans
        (X.F.ev_LL_g e k k' _ hh)).symm
        ((ev_res z _ hw (le_pull hz') _).trans (ha k' L z _ hz' Q' hQ' ez')).symm)))
    rw [hwt, ← mul_assoc, ← Units.val_mul]
    have : (∏ ix, X.F.TAt k k' (z ≫ X.inc) hh ix ^ (-e ix)) * ∏ ix, X.F.TAt k k' (z ≫ X.inc) hh ix ^ e ix = 1 := by
      rw [← Finset.prod_mul_distrib]; simp
    rw [this, Units.val_one, one_mul]⟩
  refine ⟨s, funext fun p => funext fun P => ?_⟩
  haveI : _root_.IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  refine eq_of_field_algHoms (K := c.F) fun L _ _ ψ => ?_
  obtain ⟨P', hP⟩ := exists_frMap ψ P
  obtain ⟨k, hz⟩ := exists_chart_of_isLocalRing X.F.cover (X.pt P' ≫ X.inc)
  obtain ⟨Q, t, hQ, ht⟩ := X.exists_chartFr_frBor P' k hz
  have hc : coef s k (X.pt P') hz = evR Xo c f Q := ha k L _ _ hz Q hQ (X.pt_frBor ht)
  rw [← FlagTan.evR_eq hf.1 hP, FlagTan.evR_frBor hf ht, ← hc]
  refine (val_frMap s hP).symm.trans ?_
  convert val_eq s hQ ht

theorem toRule_injective [IsReduced X.Yo] {s s' : X.SecO e} (h : toRule s = toRule s') : s = s' := by
  refine TieUniq.sec_ext fun j => ext_ev_field fun S _ w hw => ?_
  obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j PUnit.unit, rfl⟩
  have hz : ⊤ ≤ (w ≫ X.inc) ⁻¹ᵁ X.F.U k := fun p hp => mem_pull.1 (hw hp)
  obtain ⟨_, h'⟩ := exists_alg_chartFr w
  obtain ⟨Q, hQ, rfl⟩ := h' k hz
  exact (val_chartFr s hQ).symm.trans (((evR_toRule_of_isReduced s Q).symm.trans
    ((congrArg (evR Xo c · Q) h).trans (evR_toRule_of_isReduced s' Q))).trans (val_chartFr s' hQ))

end FlagCover

end GlobalTheory.FlagMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteUnitaryRationalPointFiniteAndInfin
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.RatPt

open GlobalTheory.BCT.TrKer GlobalTheory.BCT.FinPart

theorem coord_pInf_algebraMap {E : Type} [Field E] [NumberField E] [IsCMField E] (v : InfinitePlace E) (e : E) :
    coord v.embedding (pInf E (algebraMap E (Ad E) e)) = v.embedding e := by
  have hv : (InfinitePlace.mk v.embedding) = v := InfinitePlace.mk_embedding v
  have h : (InfinitePlace.mk v.embedding).embedding = v.embedding := by rw [hv]
  simp only [coord, h, if_true, Pi.evalRingHom_apply]
  rw [pInf_algebraMap, hv]

theorem ratGL_mem_UA {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (γ : UE E n) :
    ratGL E n γ.1 ∈ UA E n := by
  have hγ : cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val * 1 * γ.1.val = 1 := γ.2
  change cT (conjAd E) (ratGL E n γ.1).val * 1 * (ratGL E n γ.1).val = 1
  have hc : cT (conjAd E) (ratGL E n γ.1).val =
      (algebraMap E (Ad E)).mapMatrix (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.val) := by
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
    exact conjAd_algebraMap _
  have hr : (ratGL E n γ.1).val = (algebraMap E (Ad E)).mapMatrix γ.1.val := rfl
  rw [hc, hr, mul_one, ← map_mul, ← map_one (algebraMap E (Ad E)).mapMatrix, ← hγ, mul_one]

theorem ratPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), ∃ r ∈ ratU E n, splitFin E n r = finPt γ ∧ ∀ v : InfinitePlace E, cEmb v.embedding r = GeneralLinearGroup.map v.embedding γ.1 := by
  intro E _ _ _ n γ
  refine ⟨⟨ratGL E n γ.1, ratGL_mem_UA γ⟩, ⟨γ.1, rfl⟩, ?_, ?_⟩
  · set r : UA E n := ⟨ratGL E n γ.1, ratGL_mem_UA γ⟩
    have hpr : GeneralLinearGroup.map (pFin E) (ratGL E n γ.1) = ratF E n γ.1 := by
      apply Units.ext
      ext i j
      rfl
    have hi : (finPt γ).1⁻¹ * r ∈ infU E n := by
      rw [infU, MonoidHom.mem_ker, MonoidHom.comp_apply, map_mul, map_mul, map_inv, map_inv]
      change (pU (finPt γ))⁻¹ * GeneralLinearGroup.map (pFin E) (ratGL E n γ.1) = 1
      rw [pU_finPt, hpr, inv_mul_cancel]
    have he : r = (finPt γ).1 * (⟨_, hi⟩ : infU E n).1 := by
      simp only [mul_inv_cancel_left]
    rw [he, splitFin_mul]
  · intro v
    apply Units.ext
    ext i j
    change coord v.embedding (pInf E (algebraMap E (Ad E) (γ.1.val i j))) = v.embedding (γ.1.val i j)
    exact coord_pInf_algebraMap v _

end GlobalTheory.BCT.RatPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantOpenNatCastIsUnitNonZeroDivisor
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_schemeTheoreticallyDominant_isUnit_natCast (T : Scheme.{0}) (c : ℕ)
    (hc : ∀ (U : T.Opens) (f : Γ(T, U)), (c : Γ(T, U)) * f = 0 → f = 0) :
    ∃ (U : Scheme.{0}) (j : U ⟶ T), IsSchemeTheoreticallyDominant j ∧ IsUnit (c : Γ(U, ⊤)) := by
  refine ⟨(T.basicOpen (c : Γ(T, ⊤))).toScheme, (T.basicOpen (c : Γ(T, ⊤))).ι, ?_, ?_⟩
  · refine isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine T T (𝟙 T) _ ?_
    intro U V hU _ _ b hb
    have key : ∀ (n : ℕ) (b : Γ(T, U)), (c : Γ(T, U)) ^ n * b = 0 → b = 0 := by
      intro n
      induction n with
      | zero => intro b h; simpa using h
      | succ n ih =>
        intro b h
        exact hc U b (ih _ (by rw [← _root_.mul_assoc, ← pow_succ]; exact h))
    have hD : T.basicOpen (c : Γ(T, U)) = U ⊓ T.basicOpen (c : Γ(T, ⊤)) := by
      rw [← T.basicOpen_res (c : Γ(T, ⊤)) (homOfLE (le_top : U ≤ ⊤)).op, map_natCast]
    have h0 : T.presheaf.map (homOfLE (T.basicOpen_le (c : Γ(T, U)))).op b = 0 := by
      refine TopCat.Presheaf.section_ext T.sheaf _ _ 0 (fun x hx => ?_)
      show T.presheaf.germ _ x hx (T.presheaf.map _ b) = T.presheaf.germ _ x hx 0
      rw [TopCat.Presheaf.germ_res_apply, map_zero]
      exact hb x _ (hD ▸ hx).2
    letI := hU.isLocalization_basicOpen (c : Γ(T, U))
    obtain ⟨⟨m, n, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (c : Γ(T, U)))
        Γ(T, T.basicOpen (c : Γ(T, U))) b).mp h0
    exact key n b hm
  · have := (T.toRingedSpace.isUnit_res_basicOpen (c : Γ(T, ⊤))).map
      (T.basicOpen (c : Γ(T, ⊤))).topIso.inv.hom
    exact (congrArg IsUnit ((congrArg _ (map_natCast _ c)).trans (map_natCast _ c))).mp this

end GlobalTheory
end

