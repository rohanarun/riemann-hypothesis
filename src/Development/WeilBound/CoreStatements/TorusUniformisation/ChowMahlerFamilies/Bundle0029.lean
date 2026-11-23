module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0171
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ModelObjectSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.ModelSectionsTransport

theorem exists_common {F K L : Type} [Field F] [Field K] [Field L] (g : F →+* K) (h : F →+* L) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (i : K →+* Ω) (j : L →+* Ω), i.comp g = j.comp h := by
  letI := g.toAlgebra
  letI := h.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[F] L)
  letI : Field ((K ⊗[F] L) ⧸ m) := Ideal.Quotient.field m
  let q : K ⊗[F] L →+* AlgebraicClosure ((K ⊗[F] L) ⧸ m) :=
    (algebraMap ((K ⊗[F] L) ⧸ m) (AlgebraicClosure ((K ⊗[F] L) ⧸ m))).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure ((K ⊗[F] L) ⧸ m), inferInstance, inferInstance,
    q.comp Algebra.TensorProduct.includeLeftRingHom,
    q.comp (Algebra.TensorProduct.includeRight : L →ₐ[F] K ⊗[F] L).toRingHom, ?_⟩
  have e := Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := F) (A := K) (B := L)
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  exact congrArg (q.comp ·) e

theorem exists_transport {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {F K L : Type} [Field F] [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L] [CharZero F]
    (t : SAB H (Sp F)) (ht : IsPrincipal t) (g : F →+* K) (h : F →+* L)
    (I : TateIso D L (Over.mk (spMap h) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) :
    ∃ J : TateIso D K (Over.mk (spMap g) ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)),
      ∀ n, 0 < n → ∀ v (s : 𝟙_ (Over (Sp F)) ⟶ t.G), toUnit _ ≫ s = I.ev n v → toUnit _ ≫ s = J.ev n v := by
  obtain ⟨Ω, _, _, i, j, hij⟩ := exists_common g h
  haveI : CharZero K := charZero_of_injective_ringHom g.injective
  haveI : CharZero L := charZero_of_injective_ringHom h.injective
  let uK : Over.mk (spMap (i.comp g)) ⟶ Over.mk (spMap g) :=
    Over.homMk (spMap i) (spMap_comp g i).symm
  let uL : Over.mk (spMap (i.comp g)) ⟶ Over.mk (spMap h) :=
    Over.homMk (spMap j) (by rw [hij, spMap_comp]; rfl)
  obtain ⟨I', -, hI'⟩ := GlobalTheory.FullPoint.exists_tateIso_up (D := D)
    GlobalTheory.abelianSchemeLaws_all.1 (SabModel.pol t ht) t.act.act j uL rfl I
  obtain ⟨J, hJ⟩ := PositivityTheory.Xgn.tate_isomorphism_descends E H D (Sp F) (SabModel.pol t ht)
    t.act.act t.act.hom K Ω i _ _ uK rfl I'
  refine ⟨J, fun n hn v s hs => ?_⟩
  apply GlobalTheory.TorsionFieldExt.comp_injective uK t.G
  show uK ≫ (toUnit _ ≫ s) = uK ≫ J.ev n v
  rw [← hJ n v hn, hI' n v, ← hs, ← Category.assoc,
    toUnit_unique (uK ≫ toUnit _) (uL ≫ toUnit _), Category.assoc]
  rfl

end PositivityTheory.Xgn.ModelSectionsTransport

theorem PositivityTheory.Xgn.model_object_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (F : IntermediateField ℚ ℂ) (hK : KA l ≤ F) (t : SAB H (Sp F)), IsPrincipal t → l.A = 1 → (∀ (k : Type) [Field k] [IsAlgClosed k] (g : F →+* k) (τ : 𝓞 E →+* k), (τ H.rt = g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.p) ∧ (τ H.rt ≠ g (IntermediateField.inclusion hK (baseKA l).ρ) → LieMult t.act (spMap g) τ D.q)) → ∀ I : TateIso D ℂ (Over.mk (spMap (algebraMap F ℂ)) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (∀ a : D.La, ∃ s : 𝟙_ (Over (Sp F)) ⟶ t.G, toUnit _ ≫ s = I.ev l.M a) → ∃ o : Obj D l (baseKA l) (spMap (IntermediateField.inclusion hK).toRingHom), o.t = t := by
  intro E _ _ _ H D l F hK t ht hA hLie I hsec
  obtain ⟨hpr, ham, hkt⟩ := id ht
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp l.coprime)
  choose eta heta using fun a => hsec (e' • a)
  have inj := GlobalTheory.TorsionFieldExt.comp_injective (x := 𝟙 (Sp F))
    (toUnit (Over.mk (spMap (algebraMap F ℂ)))) t.G
  refine ⟨⟨t, hpr, ham, hkt, eta, fun a c => inj ?_, fun a ha => inj ?_, fun _ => 1,
    fun _ _ => (mul_one 1).symm, fun _ => rfl, ?_⟩, rfl⟩
  · show toUnit _ ≫ eta (a + c) = toUnit _ ≫ (eta a * eta c)
    rw [comp_mul, heta, heta, heta, smul_add, I.add]
  · show toUnit _ ≫ eta a = toUnit _ ≫ 1
    rw [MonObj.comp_one, heta]
    obtain ⟨c, hc⟩ := GlobalTheory.FullPoint.exists_eq_nsmul (D := D) l ((mul_comm _ _).trans l.prod) he' ha
    exact (I.ker _ hM _).mpr ⟨c, hc⟩
  intro k _ _ x β hx
  obtain ⟨g, rfl⟩ : ∃ g : F →+* k, x = spMap g :=
    ⟨(Spec.preimage x).hom, by simp [spMap, Spec.map_preimage]⟩
  have hβ : β = g.comp (IntermediateField.inclusion hK).toRingHom :=
    GlobalTheory.FullPoint.spMap_inj (by rw [spMap_comp]; exact hx.symm)
  subst hβ
  obtain ⟨J, hJ⟩ := PositivityTheory.Xgn.ModelSectionsTransport.exists_transport D t ht g (algebraMap F ℂ) I
  refine ⟨fun τ => hLie k g τ, J, ?_, fun a => ?_, fun a ha => ?_⟩
  · have a1 : J.ζ l.A = 1 := by
      have h := J.ζ_prim l.A l.A_pos
      rw [hA] at h ⊢
      exact IsPrimitiveRoot.one_right_iff.mp h
    have b1 : (baseKA l).ζ = 1 := by
      have h := (baseKA l).ζ_prim
      rw [hA] at h
      exact IsPrimitiveRoot.one_right_iff.mp h
    rw [a1, b1, map_one, Units.val_one]
  · simp only [MonObj.comp_one]
    symm
    rw [hA]
    exact (J.ker 1 one_pos a).mpr ⟨a, (one_smul ℕ a).symm⟩
  · rw [hJ l.M hM (e' • a) (eta a) (heta a)]
    obtain ⟨c, hc⟩ := GlobalTheory.FullPoint.exists_eq_nsmul (D := D) l l.prod he ha
    have h0 : J.ev l.M (e • a) = 1 := (J.ker _ hM _).mpr ⟨c, hc⟩
    calc J.ev l.M (e' • a) = J.ev l.M (e • a) * J.ev l.M (e' • a) := by rw [h0, _root_.one_mul]
      _ = J.ev l.M a := by rw [← J.add, ← add_smul, hee, one_smul]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ShimuraDatumTateIsomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.ShimuraDatumTate

open _root_.GlobalTheory GlobalTheory.PointUnif

theorem adj_of_weil {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {G : Over S}
    [GrpObj G] {y : Sp ℂ ⟶ S} {g : ℕ} {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {act : OAct (𝓞 E) G} {L : LB G.left}
    {ty : Fin g → (E →+* ℂ)} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] {P : La →+ (Fin g → ℂ)}
    {EF : LinearMap.BilinForm ℤ La} (hL : L.IsLB) (he : IsExp e) (hker : ∀ z, e z = 1 ↔ z ∈ P.range)
    (hP : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i)
    (hlin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ act.act a)
    (hweil : ∀ (k : ℕ) (a b : La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      Out.WeilIs G L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hros : ∀ (k : ℕ) (x x' : Over.mk y ⟶ G) (a : 𝓞 E) (c : Γ((Over.mk y).left, ⊤)ˣ), x ^ k = 1 → x' ^ k = 1 →
      Out.WeilIs G L k (x ≫ act.act a) x' c → Out.WeilIs G L k x (x' ≫ act.act (H.bar a)) c)
    (c : 𝓞 E) (x x' : La) : EF (c • x) x' = EF x (H.bar c • x') := by
  have key : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ EF (c • x) x' - EF x (H.bar c • x') := fun n hn => by
    have e1 := hweil n (c • x) x' _ hn (expNegUnit_zpow_val n _)
    have e2 := hweil n x (H.bar c • x') _ hn (expNegUnit_zpow_val n _)
    rw [exp_div_smul hP hlin] at e1 e2
    have e3 := hros n _ _ c _ (exp_div_pow he hker hn x) (exp_div_pow he hker hn x') e1
    have f := weilIs_unique_fieldPoint _ _ _ hL ℂ _ _ _ _ _ _ e3 e2
    rw [← (expNegUnit_isPrimitiveRoot hn).zpow_eq_one_iff_dvd, _root_.zpow_sub, f, mul_inv_cancel]
  exact sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    (key _ (Nat.succ_pos (EF (c • x) x' - EF x (H.bar c • x')).natAbs))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _))

theorem weil_adj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L]
    (t : SAB H (Sp L)) (ht : IsPrincipal t) (k : ℕ) (T : Over (Sp L)) (x x' : T ⟶ t.G) (a : 𝓞 E)
    (c : Γ(T.left, ⊤)ˣ) (hx : x ^ k = 1) (hx' : x' ^ k = 1)
    (h : Out.WeilIs t.G t.PP.L k (x ≫ t.act.act a) x' c) :
    Out.WeilIs t.G t.PP.L k x (x' ≫ t.act.act (H.bar a)) c := by
  letI := H.starRing
  exact (weilRosati abelianSchemeLaws_all.1.globalFns abelianSchemeLaws_all.1.cube (Sp L) (SabModel.pol t ht) (𝓞 E)
    ⟨t.act.toRingAct, t.rosatiAdj⟩ k T x x' a c hx hx').1 h

end PositivityTheory.Xgn.ShimuraDatumTate

open _root_.GlobalTheory GlobalTheory.PointUnif PositivityTheory.Xgn.ShimuraDatumTate in
theorem PositivityTheory.Xgn.shimura_datum_tate_isomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] (t : SAB H (Sp L)), IsPrincipal t → ∀ (σ : L →+* ℂ) (p q : ℕ), (∀ τ : 𝓞 E →+* ℂ, (τ H.rt = H.rt0 → LieMult t.act (spMap σ) τ p) ∧ (τ H.rt ≠ H.rt0 → LieMult t.act (spMap σ) τ q)) → ∃ D : Datum H, D.p = p ∧ D.q = q ∧ Nonempty (TateIso D ℂ (Over.mk (spMap σ) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))) := by
  intro E _ _ _ H L _ t ht σ p q hdet
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H (Sp ℂ), Nonempty (SABMap t' t (spMap σ)) :=
    ⟨_, ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.sabM ReciprocityTheory.ChartRestriction.G.Out.proved_CubePullSt (spMap σ) t⟩⟩
  have hLiso : LBIso t'.PP.L (t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨hab, hamp, hkt⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally _ _ t.G t'.G
    (spMap σ) m.cm.F _ _ t.PP.isLB t'.PP.isLB (SabModel.pol t ht).isAb m.cart hLiso
  have ht' : IsPrincipal t' := ⟨hab.proper, hamp ht.2.1, hkt ht.2.2⟩
  obtain ⟨u, Hm, χ, Ef, hAH, -, h1, h2, hF, -, hE, hbij, hweil⟩ :=
    thetaUnifAV_all (SabModel.pol t' ht') t'.PP.rig t'.PP.rigGen
  obtain ⟨g, ty, hty⟩ := AllClasses.exists_isTypeFn H p q
  obtain ⟨Φ, hΦ, hΦW⟩ := exists_push m.cart (𝟙_ _)
    (weilIs_iff_of_isGrpPullback_comm _ _ _ _ (spMap σ) m.cm.F _ _ t.PP.isLB t'.PP.isLB m.cart hLiso _) (spMap σ)
    (Category.id_comp _)
  have he₀ := isExp_push m.cart u h1 h2 Φ hΦ
  have hker₀ : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  obtain ⟨ρ, hρ⟩ := he₀.exists_rep t.act u.Λ u.discrete hker₀ fun a => by
    obtain ⟨F, hF⟩ := hF (t'.act.act a) (t'.act.hom a)
    refine ⟨F, fun z => Over.OverMorphism.ext ?_⟩
    rw [hΦ, hF, Over.comp_left _ _ _ (Φ _), hΦ]
    exact (Category.assoc _ _ _).trans ((congrArg (fun q => (u.ex z).left ≫ q) (m.act a)).trans
      (Category.assoc _ _ _).symm)
  obtain ⟨h, hh⟩ := exists_equiv_of_finrank_eq (isSplitting_embeddings (E := E)) (diagRep ty) ρ fun φ => by
    rw [finrank_eigenSub_diagRep]
    by_cases hφ : φ (H.rt : E) = H.rt0
    · rw [(hty φ).1 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).1 hφ)]
    · rw [(hty φ).2 hφ, he₀.finrank_eigenSub _ ρ hρ ((hdet _).2 hφ)]
  have he := he₀.comp_equiv h
  have hlin : ∀ (a : 𝓞 E) z, Φ (u.ex (h fun k => ty k (a : E) * z k)) = Φ (u.ex (h z)) ≫ t.act.act a :=
    fun a z => by rw [← hρ, ← hh, diagRep_apply]
  have hst : ∀ a, ∀ x ∈ u.Λ, ρ a x ∈ u.Λ := fun a x hx => by
    have := t.act.hom a
    rw [← hker₀, hρ, (hker₀ x).2 hx, MonObj.one_comp]
  letI : SMul (𝓞 E) u.Λ := ⟨fun a x => ⟨ρ a x, hst a x x.2⟩⟩
  have hsm : ∀ (a : 𝓞 E) (x : u.Λ), ((a • x : u.Λ) : _ → ℂ) = ρ a x := fun _ _ => rfl
  letI : Module (𝓞 E) u.Λ := Module.ofMinimalAxioms
    (fun a x y => Subtype.ext (by simp [hsm])) (fun a b x => Subtype.ext (by simp [hsm]))
    (fun a b x => Subtype.ext (by simp [hsm])) (fun x => Subtype.ext (by simp [hsm]))
  let P : u.Λ →+ (Fin g → ℂ) := h.symm.toLinearMap.toAddMonoidHom.comp u.Λ.subtype.toAddMonoidHom
  have hP : ∀ x, h (P x) = x := fun x => h.apply_symm_apply _
  have hrange : ∀ z, z ∈ P.range ↔ h z ∈ u.Λ := fun z =>
    ⟨by rintro ⟨x, rfl⟩; rw [hP]; exact x.2, fun hz => ⟨⟨_, hz⟩, h.symm_apply_apply z⟩⟩
  have hker : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P.range := fun z => (hker₀ _).trans (hrange z).symm
  have hPs : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x => congrFun (h.injective (by
    rw [hP, hsm, ← diagRep_apply, hh, hP]))
  have hPi : Function.Injective P := h.symm.injective.comp Subtype.val_injective
  have hPd : DiscreteTopology P.range := by
    have := u.discrete
    refine DiscreteTopology.of_continuous_injective (f := fun z : P.range => (⟨h z, (hrange _).1 z.2⟩ : u.Λ))
      ((h.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _) fun z w hzw => ?_
    exact Subtype.ext (h.injective (congrArg Subtype.val hzw))
  have hPf : Submodule.span ℝ (Set.range P) = ⊤ := by
    have e : Set.range P = (h.symm.toLinearMap.restrictScalars ℝ) '' u.Λ := by
      ext z
      exact ⟨by rintro ⟨x, rfl⟩; exact ⟨x, x.2, rfl⟩, by rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩
    rw [e, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact h.symm.surjective
  obtain ⟨Hm', hH', hH''⟩ := exists_hermForm_comp Hm hAH.1 h.toLinearMap
  have hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm' z z).re := fun z hz => by
    rw [hH'']
    exact hAH.2.1 _ (h.map_ne_zero_iff.2 hz)
  have him : ∀ x x', (hermForm Hm' (P x) (P x')).im = Ef x x' := fun x x' => by
    rw [hH'', hE]
    exact congrArg₂ (fun a b => (hermForm Hm a b).im) (hP x) (hP x')
  have hweil' : ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P b))))
        (unitOn c) := fun k a b c hk hc => by
    rw [map_smul, map_smul, hP, hP]
    exact hΦW _ _ _ _ (hweil k a b c hk hc)
  obtain ⟨D', ε, hp, hq, hε⟩ := PeriodDatum.exists_datum E H u.Λ Ef p q g ty P Hm' hty hbij
    (adj_of_weil t.PP.isLB he hker hPs hlin hweil' fun k => weil_adj t ht k _) hPs hPi hPd hPf hH' hpos him
  let P' : D'.La →+ (Fin g → ℂ) := P.comp ε.toLinearMap.toAddMonoidHom
  have hr' : P'.range = P.range := by
    ext z
    exact ⟨by rintro ⟨x, rfl⟩; exact ⟨ε x, rfl⟩,
      by rintro ⟨x, rfl⟩; exact ⟨ε.symm x, congrArg P (ε.apply_symm_apply x)⟩⟩
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, hPi.comp ε.injective, hr' ▸ hPd, ?_, Hm', hH', hpos, fun x x' => ?_⟩
    · exact (congrArg (fun x => P x i) (map_smul ε a x)).trans (hPs a _ i)
    · rw [← AddMonoidHom.coe_range, hr', AddMonoidHom.coe_range, hPf]
    · rw [hε]; exact him _ _
  have hker' : ∀ z, Φ (u.ex (h z)) = 1 ↔ z ∈ P'.range := hr' ▸ hker
  have hweil'' : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (Φ (u.ex (h ((k : ℂ)⁻¹ • P' a)))) (Φ (u.ex (h ((k : ℂ)⁻¹ • P' b))))
        (unitOn c) := fun k a b c hk hc => hweil' k (ε a) (ε b) c hk (by rw [hc, hε])
  exact ⟨D', hp, hq, ⟨expTateIso he hper hker' hlin hweil''⟩⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TrivialTypeGoodReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.Xgn.TrivialTypeGoodReduction

open _root_.GlobalTheory GlobalTheory.PointUnif GlobalTheory.EigenSplit
open scoped CategoryTheory.Obj

noncomputable def fibPol {X : Scheme.{0}} (P : Out.PolAV X) {z : Sp ℂ ⟶ X} {A : Over (Sp ℂ)} [GrpObj A]
    {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A z φ) : Out.PolAV (Sp ℂ) :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

theorem dim_eq_zero {E : Type} [Field E] [NumberField E] {X : Scheme.{0}} (P : Out.PolAV X)
    (act : OAct (𝓞 E) P.A) (y : Sp ℂ ⟶ X) (hy : ∀ τ : 𝓞 E →+* ℂ, LieMult act y τ 0) : P.g = 0 := by
  classical
  have hab := P.isAb
  have := hab.comm
  have hφ := isGrpPullback_pullback P.A y
  obtain ⟨rig, hr⟩ := (fibPol P hφ).rigid
  obtain ⟨u, Hm, χ, Ef, -, -, h1, h2, hF, -⟩ := thetaUnifAV_all (fibPol P hφ) rig hr
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ _) y (Category.id_comp _).symm
  have he := isExp_push hφ u h1 h2 Φ hΦ
  have hker : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  obtain ⟨ρ, hρ⟩ := he.exists_rep act u.Λ u.discrete hker fun a => by
    obtain ⟨F, hF⟩ := hF ((OAct.pullback y P.A act).act a) ((OAct.pullback y P.A act).hom a)
    have hact : ((OAct.pullback y P.A act).act a).left ≫ pullback.fst P.A.hom y =
      pullback.fst P.A.hom y ≫ (act.act a).left := pullback.lift_fst _ _ _
    refine ⟨F, fun z => Over.OverMorphism.ext ?_⟩
    refine (hΦ _).trans ((congrArg (fun q => q.left ≫ pullback.fst P.A.hom y) (hF z)).trans ?_)
    refine (Category.assoc _ _ _).trans ((congrArg ((u.ex z).left ≫ ·) hact).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (act.act a).left) (hΦ _).symm)
  have h0 := (eigenEquiv (isSplitting_embeddings (E := E)) ρ).finrank_eq
  rw [Module.finrank_fin_fun, Module.finrank_pi_fintype] at h0
  exact h0.trans (Finset.sum_eq_zero fun i _ => he.finrank_eigenSub act ρ hρ (hy _))

theorem isIso_of_dim_zero {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (hB : IsAbelianScheme B)
    (hg : SmoothOfRelativeDimension 0 B.hom) : IsIso B.hom := by
  have := hB.proper
  have := hB.geomConnected
  have := hB.smooth
  have : Etale B.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hg
  have hs : eSec B ≫ B.hom = 𝟙 (Sp k) := Models.RankZero.section_w η[B]
  obtain ⟨ho, hcl⟩ := isOpenImmersion_and_isClosedImmersion_of_section_of_etale B.hom (eSec B) hs
  have : ConnectedSpace B.left := (GroupConn.connectedSpace_group _ B).1
  have hne : (Set.range (eSec B)).Nonempty := ⟨_, (default : PrimeSpectrum k), rfl⟩
  have hsurj : Function.Surjective (eSec B) :=
    Set.range_eq_univ.1 (IsClopen.eq_univ ⟨(eSec B).isClosedEmbedding.isClosed_range,
      (eSec B).isOpenEmbedding.isOpen_range⟩ hne)
  have : Epi (eSec B).base := (TopCat.epi_iff_surjective _).2 hsurj
  have : IsIso (eSec B) := IsOpenImmersion.isIso _
  have : IsIso (eSec B ≫ B.hom) := by
    rw [hs]
    exact inferInstanceAs (IsIso (𝟙 (Sp k)))
  exact IsIso.of_isIso_comp_left (eSec B) B.hom

end PositivityTheory.Xgn.TrivialTypeGoodReduction

theorem PositivityTheory.Xgn.trivial_type_good_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (t : SAB H (Sp L)), IsPrincipal t → (∀ (σ : L →+* ℂ) (τ : 𝓞 E →+* ℂ), LieMult t.act (spMap σ) τ 0) → ∃ t' : SAB H (Sp (𝓞 L)), Nonempty (SABMap t t' (spMap (algebraMap (𝓞 L) L))) := by
  intro E _ _ _ H L _ _ t ⟨hp, hA, hK⟩ hL
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hp, t.semi.geomConnected⟩
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim L t.G hab
  obtain ⟨σ⟩ : Nonempty (L →+* ℂ) := inferInstance
  obtain rfl : g = 0 := PositivityTheory.Xgn.TrivialTypeGoodReduction.dim_eq_zero
    (GlobalTheory.GenericPol.toPolAV t g hg hp hA hK) t.act (spMap σ) (hL σ)
  exact ⟨GlobalTheory.Models.Inhab.zeroTriple H _, GlobalTheory.Models.RankZero.nonempty_sabMap
    (PositivityTheory.Xgn.TrivialTypeGoodReduction.isIso_of_dim_zero t.G hab hg) (GlobalTheory.Models.RankZero.isIso_zeroTriple _) _⟩
end

