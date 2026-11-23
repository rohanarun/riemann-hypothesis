module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ShortRuleRepresentationChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordOfIsPullDegId
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SameCoord


set_option maxHeartbeats 1600000 in
theorem psiCoord_of_isPullDeg_id {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D' : DegPre R}
    (hD : IsPullDeg (RingHom.id R) D D') (x : D'.X) (r : R) (hr : PsiCoord D (hD.xe x) r) :
    ∃ u : Rˣ, PsiCoord D' x (u * r) := by
  obtain ⟨j, hj, h, hr⟩ := hr
  have hs := specOf_id R
  set Φ := hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) with hΦ
  have hc : (D'.c x).left ≫ Φ = (D.c (hD.xe x)).left := by
    rw [hΦ, hD.c_pr x]
    exact (congrArg (· ≫ (D.c (hD.xe x)).left) hs).trans (Category.id_comp _)
  obtain ⟨q, hq⟩ := exists_chart D'.P.isLB ((D'.c x).left (closedPoint R))
  have hq' : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D'.c x).left ⁻¹ᵁ D'.P.L.U q :=
    ((IsLocalRing.closedPoint_mem_iff _).1 hq).ge
  have hp : ∀ y : Spec (CommRingCat.of R), Φ ((D'.c x).left y) ∈ D.P.L.U (j PUnit.unit) := fun y =>
    (congrArg (fun g => g y ∈ D.P.L.U (j PUnit.unit)) hc).mpr (hj trivial)
  have hV : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      (D'.c x).left ⁻¹ᵁ ((D.P.L.pull Φ).U (fun _ => j PUnit.unit) ⊓ D'.P.L.U q) := fun y _ =>
    ⟨mem_pull.2 (hp y), hq' trivial⟩
  let u₀ : Γ(Spec (CommRingCat.of R), ⊤)ˣ := res hV (pullU (D'.c x).left _ (hD.w.s (fun _ => j PUnit.unit, q)))
  let u : Rˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom u₀
  have hu : DegPre.toOpen (R := R) ⊤ u = u₀.val := by
    show ((Spec (CommRingCat.of R)).presheaf.map (𝟙 _)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u₀.val)) = _
    rw [CategoryTheory.Functor.map_id]
    exact congrArg (fun g => g.hom u₀.val) (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
  have h' : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D'.P.L (K := PUnit) (fun _ => D'.xK x) (fun _ => -1)).U (fun _ => q) :=
    fun z _ => Set.mem_iInter.2 fun _ => hq' (x := jK R z) trivial
  refine ⟨u, fun _ => q, hq', h', ?_⟩
  apply TopCat.Presheaf.section_ext (TK R).left.sheaf
  intro z hz
  have hF : jFK (R := R) (FractionRing R) = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
    simp
  have hFz : jFK (R := R) (FractionRing R) z = z := by rw [hF]; rfl
  have m₁ : Φ (D'.xK x (jFK (R := R) (FractionRing R) z)) ∈ D.P.L.U (j PUnit.unit) := by
    rw [hFz]; exact hp (jK R z)
  have m₂ : D'.xK x (jFK (R := R) (FractionRing R) z) ∈ D'.P.L.U q := by
    rw [hFz]; exact hq' (x := jK R z) trivial
  have m₃ : D.xK (hD.xe x) (jFK (R := R) (FractionRing R) z) ∈ D.P.L.U (j PUnit.unit) := by
    rw [hFz]; exact hj (x := jK R z) trivial
  have pm := pmaps_psi hD (FractionRing R) (by
    have : spMap (RingHom.id R) = 𝟙 _ := hs
    rw [this, Category.comp_id]) x _ (𝟙 _) z j (fun _ => q) (fun _ => m₁) (fun _ => m₂)
  rw [Category.comp_id, Fintype.prod_unique] at pm
  have pm' := (gm_pullGen D.P.L (fun _ : PUnit => D.xK (hD.xe x)) _ (D.psi (hD.xe x)) (jFK (R := R) (FractionRing R)) (𝟙 _) z j
    (Set.mem_iInter.2 fun _ => m₃)).symm.trans (pm.trans (congrArg (_ * ·)
      (gm_pullGen D'.P.L (fun _ : PUnit => D'.xK x) _ (D'.psi x) (jFK (R := R) (FractionRing R)) (𝟙 _) z (fun _ => q)
    (Set.mem_iInter.2 fun _ => m₂))))
  rw [hF, Category.comp_id, Category.id_comp, Category.id_comp, zpow_neg_one, eq_inv_mul_iff_mul_eq] at pm'
  have a₁ : gm (jK R) z ⊤ u₀ = gw hD.w (D'.xK x) z (j PUnit.unit) q :=
    (gm_res (jK R) z hV trivial _).trans (gm_pull (jK R) (D'.c x).left z _ (hV (x := jK R z) trivial) _)
  have a₂ := gm_res (𝟙 (TK R).left) z h hz ((D.psi (hD.xe x)).s j)
  have a₃ := gm_res (𝟙 (TK R).left) z h' hz ((D'.psi x).s (fun _ => q))
  have k := congrArg Units.val ((congrArg₂ (fun a b : ((TK R).left.presheaf.stalk z)ˣ => a * b) a₁ a₂).trans (pm'.trans a₃.symm))
  rw [Units.val_mul, gm_val (jK R) z ⊤ trivial, gm_val _ z _ hz, gm_val _ z _ hz] at k
  rw [map_mul, map_mul, hu, hr]
  exact (map_mul _ _ _).trans k

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}


set_option maxHeartbeats 1600000 in
theorem exists_move (hU : UnifBaseChangeSt) (h5 : Laws5) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    (hR : AdmBase R I) {t t' : SAB H (Sp R)} (m : SABMap t' t (𝟙 _)) (P : PELUnif I t) :
    ∃ (P' : PELUnif I t') (hD : IsPullDeg (RingHom.id R) P.D.toPre P'.D.toPre),
      ∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y := by
  let _ := H.starRing
  have hs := specOf_id R
  have gp₁ : IsGrpPullback t'.G t.G (specOf (RingHom.id R)) m.φ := m.cart.congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback t.G (specOf (RingHom.id R)))
  have gpG : IsGrpPullback P.A.A t.G (jK R) (P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R)) := by
    have := P.U.gen_hom
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr
      (Category.id_comp _) rfl
  have gp₂ : IsGrpPullback ((Over.pullback (jK R)).obj t'.G) t.G (jK R)
      (pullback.fst t'.G.hom (jK R) ≫ m.φ) :=
    ((isGrpPullback_pullback t'.G (jK R)).comp m.cart).congr (Category.comp_id _) rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp₂ gpG
  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (P.A.L.pull eA.hom.left) (P.U.LG.L.pull (pullback.fst t'.G.hom (jK R) ≫ bc.hom.left ≫
      pullback.fst t.G.hom (specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := eA.hom.left ≫ P.U.gen.inv.left)
      (chartPullSame P.A.L (fun _ => eA.hom.left) (fun _ => P.U.gen.hom.left) _ _ fun _ => by
        rw [Category.assoc, hgi, Category.comp_id])
      (chartPullSame P.U.LG.L _ (fun _ => pullback.fst t.G.hom (jK R)) _ _ fun _ => by
        rw [hbc, ← heA]; simp only [Category.assoc]) P.U.ext
  obtain ⟨wL', he', gL, rL⟩ := rigIso_congr P.bundle m.cm m.lin hbc
    (e := specOf (RingHom.id R)) (hs.trans m.base.symm)
  obtain ⟨Wo, hWo, hψW⟩ := h5.psiOnExists R I hR P.D
  have hgen : (specOf (RingHom.id R)).base (genericPoint (Spec (CommRingCat.of R))) ∈ Wo := by
    rw [hs]; exact hWo
  have hI : I.map (RingHom.id R) ≤ I := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', hLG, hgenU, hPU⟩ := hU R R I I hR hR (RingHom.id R) hI P.D P.A t.G t.semi P.U
    Wo hψW hgen t'.G bc mbc P.A rfl eA mE wA t'.PP wL' he' gL rL
  have a₃ : ∀ x, (t'.act.act x).left ≫ m.φ = m.φ ≫ (t.act.act x).left := m.act
  have hbcact : ∀ x, t'.act.toRingAct.act x ≫ bc.hom =
      bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.toRingAct.act x) := by
    intro x
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (t.act.act x)).left ≫
          pullback.fst t.G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (t.act.act x).left :=
        pullback.lift_fst _ _ _
      show (t'.act.act x ≫ bc.hom).left ≫ _ =
        (bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.act x)).left ≫ _
      rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, hbc, ← Category.assoc, hbc, a₃]
    · exact (Over.w (t'.act.act x ≫ bc.hom)).trans
        (Over.w (bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (t.act.act x))).symm
  have actA : ∀ x, (P.oA.act x).left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) =
      P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have extA : ∀ x, (Over.pullback (jK R)).map (t'.act.toRingAct.act x) ≫ U''.gen.hom =
      U''.gen.hom ≫ P.oA.act x := by
    intro x
    rw [hgenU]
    apply Over.OverMorphism.ext
    apply gpG.1.hom_ext
    · have a₁ : ((Over.pullback (jK R)).map (t'.act.act x)).left ≫ pullback.fst t'.G.hom (jK R) =
          pullback.fst t'.G.hom (jK R) ≫ (t'.act.act x).left := pullback.lift_fst _ _ _
      show ((Over.pullback (jK R)).map (t'.act.act x) ≫ eA.hom).left ≫ _ = (eA.hom ≫ P.oA.act x).left ≫ _
      rw [Over.comp_left, Category.assoc, heA, ← Category.assoc, a₁, Category.assoc, a₃, Over.comp_left,
        Category.assoc, actA, reassoc_of% heA]
    · rw [Over.w, Over.w]
  obtain ⟨mod'', oD'', xl, -, lin'', w0''⟩ := h5.oLinBaseChange R R I I hR hR (RingHom.id R) P.D P.A t.G P.U
    t'.G bc mbc P.A D'' hD U'' hPU (𝓞 E) P.oD P.oA t.act.toRingAct P.lin t'.act.toRingAct hbcact
    P.oA extA
  exact ⟨{ D := D'', mod := mod'', oD := oD'', A := P.A, oA := P.oA, U := U'', bundle := hLG, lin := lin''
           w0 := w0'' H.w0 P.w0 }, hD, xl⟩

theorem exists_equiv_psiCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (t t' : SAB H (Sp R)) (_ : SABMap t' t (𝟙 _)) (U : PELUnif (maximalIdeal R) t) (U' : PELUnif (maximalIdeal R) t'), IsNoetherianRing R → IsIntegrallyClosed R → IsAdicComplete (maximalIdeal R) R → ∃ e : U.D.toPre.X ≃ₗ[𝓞 E] U'.D.toPre.X, ∀ χ r, PsiCoord U.D.toPre χ r → ∃ u : Rˣ, PsiCoord U'.D.toPre (e χ) (u * r) := by
  intro E _ _ _ H R _ _ _ _ t t' m U U' hN hC hA
  letI := H.starRing
  have hR : AdmBase R (maximalIdeal R) := ⟨hN, inferInstance, hC, hA⟩
  obtain ⟨-, -, -, h4, h5, h6⟩ := GlobalTheory.allSixLaws
  obtain ⟨P, hD₁, xl₁⟩ := exists_move h4.unifBaseChange h5 hR m U
  obtain ⟨wL, g₀, m₀⟩ := exists_iso_of_eq (U'.bundle.trans P.bundle.symm)
  obtain ⟨hD₂, -, holin⟩ := h6.unifUniq R _ hR P.D U'.D P.A U'.A t'.G t'.semi P.U U'.U wL g₀ m₀
  obtain ⟨xl₂, -⟩ := holin (𝓞 E) P.oD U'.oD P.oA U'.oA t'.act.toRingAct P.lin U'.lin
  let e₁ : P.D.toPre.X ≃ₗ[𝓞 E] U.D.toPre.X := { hD₁.xe with map_smul' := xl₁ }
  let e₂ : U'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD₂.xe with map_smul' := xl₂ }
  refine ⟨e₁.symm.trans e₂.symm, fun χ r hr => ?_⟩
  have k₁ : hD₁.xe (e₁.symm χ) = χ := e₁.apply_symm_apply χ
  have k₂ : hD₂.xe (e₂.symm (e₁.symm χ)) = e₁.symm χ := e₂.apply_symm_apply _
  obtain ⟨u₁, hu₁⟩ := psiCoord_of_isPullDeg_id hD₁ (e₁.symm χ) r (by rw [k₁]; exact hr)
  obtain ⟨u₂, hu₂⟩ := psiCoord_of_isPullDeg_id hD₂ (e₂.symm (e₁.symm χ)) _ (by rw [k₂]; exact hu₁)
  exact ⟨u₂ * u₁, by rw [Units.val_mul, mul_assoc]; exact hu₂⟩

end GlobalTheory.SameCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SelfDualLatticeOccurs
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem GlobalTheory.selfDual_lattice_occurs : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r → E)) (f : ℕ → Dw.La →ₗ[𝓞 E] Λ'), l.A = 1 → σ' (baseKA l).ρ = H.rt0 → IsTypeFn H Dw.p Dw.q ty → ModelBase M → (∀ k, (M.X k).Gm = Gm ∧ (M.X k).ξ0 = ξ₀) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → Λ'.FG → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm v y) = n) ↔ v ∈ Λ') → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ v, f (n * m) a = f n a + n • v) → (∀ n : ℕ, 0 < n → (∀ a, (∃ v, f n a = n • v) ↔ ∃ v, a = n • v) ∧ ∀ a', ∃ a v, a' = f n a + n • v) → (∀ n : ℕ, 0 < n → ∀ a a', ∃ z : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm (f n a) (f n a')) - (Dw.EF a a' : ℤ) = n * z) → ∃ (k : Fin F.n) (γ : GL (Fin r) E), (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ (∀ v, v ∈ Λ' ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ (M.X k).Λ) ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ (M.X k).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f l.M a : Fin r → E) = (M.φ k (F.t k a) : Fin r → E) + l.M • w := by
  intro hH E _ _ _ H Dw l Xo σ' g ty F r M ξ₀ Gm φ Λ' f hA hσ hty hM hk hφ hfg hsp hsd hc hb hi
  have hξ : cc (-ξ₀) = -(-ξ₀) := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg, h]
  obtain ⟨D', φ', hp, hq, hr, hφ'⟩ := GlobalTheory.T.exists_latticeDatum_of_selfDual_lattice E H Dw r (-ξ₀) Gm φ Λ' hξ hφ hfg hsp hsd
  let e : D'.La ≃ₗ[𝓞 E] Λ' := (LinearEquiv.ofInjective φ' hφ'.1).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ x, φ' (e.symm x) = (x : Fin r → E) := fun x => by
    have : ∀ y, ((e y : Λ') : Fin r → E) = φ' y := fun y => rfl
    rw [← this, e.apply_symm_apply]
  obtain ⟨k, gam, hg1, hg2⟩ := GlobalTheory.allClassesSt_of_hasseNorm hH E H Dw l Xo σ' g ty F hA hσ hty D'
    (fun n => e.symm.toLinearMap ∘ₗ f n) hp hq
    ⟨fun n m hn hm a => by
      obtain ⟨v, hv⟩ := hc n m hn hm a
      exact ⟨e.symm v, by simp [hv]⟩,
     fun n hn => ⟨fun a => by
      rw [← (hb n hn).1 a]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨e v, ?_⟩
        rw [← map_nsmul, ← hv]
        simp
      · rintro ⟨v, hv⟩
        exact ⟨e.symm v, by simp [hv]⟩,
      fun a' => by
        obtain ⟨a, v, hv⟩ := (hb n hn).2 (e a')
        refine ⟨a, e.symm v, ?_⟩
        apply e.injective
        simp [hv]⟩⟩
    (fun n hn a a' => by
      obtain ⟨z, hz⟩ := hi n hn a a'
      refine ⟨z, ?_⟩
      have h := hφ'.2.2.2.2 (e.symm (f n a)) (e.symm (f n a'))
      rw [he, he] at h
      rw [← h] at hz
      exact_mod_cast hz)
  let ψ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hψ : ∀ a, ψ a = (M.φ k a : Fin r → E) := fun a => rfl
  have hrange : Set.range ψ = ((M.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (M.φ k a).2
    · intro hv
      exact ⟨(M.φ k).symm ⟨v, hv⟩, by rw [hψ, LinearEquiv.apply_symm_apply]⟩
  obtain ⟨γ, hγ1, hγ2⟩ := _root_.GlobalTheory.IsoExt.exists_unitary_of_isometry E H D' (F.Di k) r (-ξ₀) Gm φ' ψ gam hξ hφ'
    ⟨Subtype.val_injective.comp (M.φ k).injective, by rw [hrange]; exact (M.X k).Λ_span, hφ.2.2.1, hφ.2.2.2.1,
      fun x y => by
        have h := hM.ef k x y
        rw [(hk k).1, (hk k).2] at h
        exact h⟩ hg1
  refine ⟨k, γ, hγ1, fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun a ha => ?_⟩
  · have h := hγ2 (e.symm ⟨v, hv⟩)
    rw [he] at h
    rw [← h]
    exact (M.φ k _).2
  · have h := hγ2 (gam.symm ((M.φ k).symm ⟨_, hv⟩))
    rw [LinearEquiv.apply_symm_apply, hψ, LinearEquiv.apply_symm_apply] at h
    have h2 := congrArg (fun w => ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    rw [h2, ← hr]
    exact LinearMap.mem_range_self _ _
  · obtain ⟨w, hw⟩ := hg2 a ha
    refine ⟨M.φ k w, (M.φ k w).2, ?_⟩
    have h := hγ2 (e.symm (f l.M a))
    rw [he] at h
    rw [← h]
    change ψ (gam ((e.symm.toLinearMap ∘ₗ f l.M) a)) = ψ (F.t k a) + l.M • ψ w
    rw [hw, map_add (f := _), map_nsmul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ShortSpanUnitOfExactValues
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortSpanCompare

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
open GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation hiding zetaM
open GlobalTheory.IndefiniteRowSideFullHecke.RamifiedCoverPairIsomorphism hiding IsShortRule shortGen ShortInCusp
open GlobalTheory.GenusLatCompare GlobalTheory.LevelCoverCompare GlobalTheory.ShortDatumEq GlobalTheory.TransferCompare

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

section Generators

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)

theorem evR_of_frMap {f : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf : f ∈ sec Xo c a n) {p : TRing c.F}
    {S : Type} [CommRing S] [Algebra c.F S] (φ : p.R →ₐ[c.F] S) {y : FrPt Xo c p.R} {z : FrPt Xo c S}
    (h : FrMap φ y z) : evR Xo c f z = φ (f p y) := by
  have hT : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, φ, y, h⟩
  unfold evR evalAt
  rw [dite_eq_left hT]
  exact evalWD_framed Xo c f hf.1 S _ _ _ _ _ _ z hT.choose_spec.choose_spec.choose_spec h

variable {Δ}

end Generators

section Spans

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)

variable {Δ}

end Spans

section Claims

variable {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab) (hK : ReflexLe Dw c) (nV : ℕ)
  (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c))

variable {Δ hK nV}

end Claims

section Std

variable (Xo c) (nab : NabV Xo c)

variable {Xo c nab}

variable (Xo c nab)

variable {Xo c nab}

end Std

end GlobalTheory.ShortSpanCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMap
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.ThetaPtChg

theorem exists_chart_point {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ p ⁻¹ᵁ L.U j := by
  let q : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hq : p q ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
  refine ⟨j, fun q' _ => ?_⟩
  have : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  rw [this]
  exact hj

theorem val_of_secBC (hS : Out.SecTwistSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
    (x x' : Sp ℂ ⟶ Xo.X) (hx : x' = x) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (a : ℂ)
    (h : SecBC (RingHom.id ℂ) a x x' s s') (p : Over.mk x ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι) (v v' : ℂ)
    (hv : ∀ pt : Sp ℂ ⟶ Gx x, pt ≫ gxFst x = p.left → pt ≫ gxSnd x = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x).U (fun _ => j)) (s.f (fun _ => j)) = v)
    (hv' : ∀ pt : Sp ℂ ⟶ Gx x', pt ≫ gxFst x' = p.left → pt ≫ gxSnd x' = 𝟙 (Sp ℂ) →
      valAt' pt ((PPx x').U (fun _ => j)) (s'.f (fun _ => j)) = v') : v' = a * v := by
  subst hx
  have hid : x' = spMap (RingHom.id ℂ) ≫ x' := by
    simp [spMap]
  have h2 := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ (RingHom.id ℂ) (RingHom.id ℂ) x' x' x' hid hid).2.1
    a s s').1 h
  let pt : Sp ℂ ⟶ Gx x' := (CartesianMonoidalCategory.lift (𝟙 (Over.mk x')) p).left
  have e1 : pt ≫ gxFst x' = p.left := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_snd (𝟙 (Over.mk x')) p)
    exact this
  have e2 : pt ≫ gxSnd x' = 𝟙 (Sp ℂ) := by
    have := congrArg CommaMorphism.left (CartesianMonoidalCategory.lift_fst (𝟙 (Over.mk x')) p)
    exact this
  rw [← hv pt e1 e2, ← hv' pt e1 e2]
  exact (congrArg (valAt' pt ((PPx x').U (fun _ => j))) (h2 (fun _ => j))).trans
    ((GlobalTheory.sec_values_complex_fibre hS E H Dw l Xo x' s).1 a _ pt e2)

theorem thetaPt_change : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsThetaPt T b κ y → IsThetaPt T b' κ' y' → ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) → (∀ a, T.Pf (T.co b') (gam a) = h₀ *ᵥ T.Pf (T.co b) a) → y'.x = y.x ∧ (∀ τ i, IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co b)) z).left) (h₀⁻¹ *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) ∧ ∃ t₀ : (CAt σ)ˣ, SecBC (RingHom.id (CAt σ)) (t₀ : CAt σ) y.x y'.x y.s y'.s ∧ toC (t₀ : CAt σ) ^ 2 * (κ ^ 2 * (T.h b').det * h₀.det) = κ' ^ 2 * (T.h b).det := by
  intro hS E _ _ _ H Dw l Xo c σ g e F r M k T b hb b' hb' κ κ' y y' gam h₀ hy hy' hgam hP
  obtain ⟨hg1, hg2, hg3⟩ := hgam
  have hp := T.isPer _ hb
  have hp' := T.isPer _ hb'
  obtain ⟨hdet, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo _ g _ F k
    (T.Pf (T.co b)) (T.Pf (T.co b')) gam h₀ hp hp' hg1 hg2 hg3 hP
  have hx : y'.x = y.x := hy'.1.trans (hu.symm.trans hy.1.symm)
  refine ⟨hx, fun τ i => ?_, ?_⟩
  · refine (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F k (T.Pf (T.co b)) hp k (T.Pf (T.co b')) (Matrix.mulVecLin h₀) hp'
      hex _ _).2 ?_
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    exact hy'.2.1 τ i
  obtain ⟨gm, a, -, -, -, hbc⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c (CAt σ) y y').1 hx
  refine ⟨a, hbc, ?_⟩
  obtain ⟨hhd, hsym, hpos, -⟩ := T.norm b hb
  obtain ⟨-, w, hw⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  obtain ⟨z, hz⟩ : ∃ z, T.h b *ᵥ z = w :=
    ⟨(T.h b)⁻¹ *ᵥ w, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hhd, Matrix.one_mulVec]⟩
  obtain ⟨j, hj⟩ := exists_chart_point Xo.univ.t.PP.isLB (F.ex k (T.Pf (T.co b)) z).left
  have hmult := GlobalTheory.thetaFrame_det_mul_sq_invariant_uncond E H Dw l Xo _ g _ F k T.m (T.co ⁻¹' (M.X k).dom)
    (fun b => T.Pf (T.co b)) T.bas T.h T.ta T.c₁ T.c₂ T.fr (fun b hb => T.isPer _ hb) T.sympl T.adapt
    (fun b hb => (T.norm b hb).2.2.2) T.half₁ T.half₂ T.fr_hol T.fr_ne T.fr_coc T.fr_rig T.fr_sec
    b hb b' hb' gam h₀ hg1 hg2 hg3 hP j z hj
  have hne : thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) ≠ 0 :=
    mul_ne_zero (by rw [hz]; exact hw) (T.fr_ne j b z hb hj)
  have hw0 : (F.ex k (T.Pf (T.co b)) z).left ≫ Xo.univ.t.G.hom = (y.x : Sp ℂ ⟶ Xo.X) :=
    (Over.w (F.ex k (T.Pf (T.co b)) z)).trans hy.1.symm
  have hval := val_of_secBC hS (Xo := Xo) y.x y'.x hx y.s y'.s (toC (a : CAt σ)) hbc
    (Over.homMk (F.ex k (T.Pf (T.co b)) z).left hw0) j _ _
    (fun pt h1 h2 => hy.2.2 j z pt h1 h2 hj)
    (fun pt h1 h2 => hy'.2.2 j (h₀ *ᵥ z) pt (h1.trans (hex z).symm) h2 (by rw [hex z]; exact hj))
  apply mul_right_cancel₀ (pow_ne_zero 2 hne)
  rw [mul_assoc κ', mul_assoc κ] at hval
  generalize thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z) = S at *
  generalize thetaChar (T.ta b') T.c₁ T.c₂ (T.h b' *ᵥ (h₀ *ᵥ z)) * T.fr j (b', h₀ *ᵥ z) = S' at *
  linear_combination (-κ' ^ 2) * hmult - (T.h b').det * h₀.det * (κ' * S' + toC (a : CAt σ) * (κ * S)) * hval

end GlobalTheory.ThetaPtChg
end
end

