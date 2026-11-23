module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0533
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0547
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0560

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GagaSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

noncomputable section

namespace GlobalTheory.CompanionTheory.Gaga

open Opposite

theorem val_comp {X Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    valAt' (x ≫ φ) U f = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) := by
  unfold valAt'
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [dite_eq_left h, dite_eq_left (show ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]
    unfold valAt
    congr 1
  · rw [dite_eq_right h, dite_eq_right (show ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U from h)]

theorem app_res {X Y : Scheme.{0}} (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (φ.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (Y.presheaf.map (homOfLE (show φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U from fun _ hy => h hy)).op).hom ((φ.app U).hom a) :=
  congr($(φ.naturality (homOfLE h).op).hom a)

theorem res_pullU {X Y : Scheme.{0}} (φ : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) :
    res (show φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U from fun _ hy => h hy) (pullU φ U u) = pullU φ V (res h u) :=
  Units.ext (app_res φ h u.val).symm

def resLB {X Y : Scheme.{0}} (φ : Y ⟶ X) (L : LB X) : LB Y where
  ι := L.ι
  U i := φ ⁻¹ᵁ L.U i
  g i j := pullU φ (L.U i ⊓ L.U j) (L.g i j)

theorem isLB_resLB {X Y : Scheme.{0}} (φ : Y ⟶ X) {L : LB X} (hL : L.IsLB) : (resLB φ L).IsLB := {
  cover := by
    refine eq_top_iff.2 fun y _ => ?_
    have hy : φ y ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  g_self i := by
    refine (res_pullU φ (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) (L.g i i)).trans ?_
    exact (congrArg (pullU φ (L.U i)) (hL.g_self i)).trans (map_one _)
  cocycle i j k := by
    have h1 := res_pullU φ (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) (L.g i j)
    have h2 := res_pullU φ (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) (L.g j k)
    have h3 := res_pullU φ (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) (L.g i k)
    have h4 := congrArg (pullU φ (L.U i ⊓ L.U j ⊓ L.U k)) (hL.cocycle i j k)
    rw [map_mul] at h4
    exact (congrArg₂ (· * ·) h1 h2).trans (h4.trans h3.symm) }

theorem glue {X : Scheme.{0}} (W : ℕ → X.Opens) (hc : ⨆ D, W D = ⊤)
    (hd : Pairwise fun D D' => W D ⊓ W D' = ⊥) (U : X.Opens)
    (a : ∀ D, Γ((W D).toScheme, (W D).ι ⁻¹ᵁ U)) :
    ∃! b : Γ(X, U), ∀ D, ((W D).ι.app U).hom b = a D := by
  let V : ℕ → X.Opens := fun D => (W D).ι ''ᵁ (W D).ι ⁻¹ᵁ U
  have hV : ∀ D, V D = W D ⊓ U := fun D => by simp [V, Scheme.Hom.image_preimage_eq_opensRange_inf]
  have hle : ∀ D, V D ≤ U := fun D => by rw [hV]; exact inf_le_right
  have hcov : U ≤ iSup V := by
    intro x hx
    have hy : x ∈ (⨆ D, W D) := by rw [hc]; trivial
    obtain ⟨D, hD⟩ := Opens.mem_iSup.1 hy
    refine Opens.mem_iSup.2 ⟨D, ?_⟩
    rw [hV]
    exact ⟨hD, hx⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 V a := by
    intro D D'
    by_cases e : D = D'
    · subst e
      rfl
    · have hb : V D ⊓ V D' = ⊥ := by
        refine eq_bot_iff.2 ?_
        rw [← hd e, hV, hV]
        exact inf_le_inf inf_le_left inf_le_left
      have : Subsingleton (X.sheaf.1.obj (op (V D ⊓ V D'))) := by
        rw [hb]
        exact CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
      exact Subsingleton.elim _ _
  obtain ⟨b, hb, hu⟩ := X.sheaf.existsUnique_gluing' V U (fun D => homOfLE (hle D)) hcov a hcomp
  refine ⟨b, fun D => ?_, fun c hc' => hu c fun D => ?_⟩
  · rw [Scheme.Opens.ι_app]
    exact hb D
  · rw [← hc' D, Scheme.Opens.ι_app]
    rfl

theorem exists_factor {X : Scheme.{0}} (W : ℕ → X.Opens) (hc : ⨆ D, W D = ⊤) (x : Sp ℂ ⟶ X) :
    ∃ (D : ℕ) (x' : Sp ℂ ⟶ (W D).toScheme), x' ≫ (W D).ι = x := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have hy : x p ∈ (⨆ D, W D) := by rw [hc]; trivial
  obtain ⟨D, hD⟩ := Opens.mem_iSup.1 hy
  have hr : Set.range x ⊆ Set.range (W D).ι := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q p, Scheme.Opens.range_ι]
    exact hD
  exact ⟨D, IsOpenImmersion.lift (W D).ι x hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem gagaSections : GlobalTheory.CompanionTheory.Ar.Flat.GagaSections := by
  intro X s hp hs L hL h hhol hcomp
  obtain ⟨W, hcl, hdim, hc, hd⟩ := _root_.GlobalTheory.CompanionTheory.Gaga.exists_clopen_smoothOfRelativeDimension X s hs
  have hprop : ∀ D, IsProper ((W D).ι ≫ s) := fun D => by
    haveI : IsClosedImmersion (W D).ι :=
      IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hcl D)
    infer_instance
  have key : ∀ D, ∃ σ : (resLB (W D).ι L).Sec, ∀ (i : L.ι) (x : Sp ℂ ⟶ (W D).toScheme),
      x ≫ (W D).ι ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ ((W D).ι ⁻¹ᵁ L.U i) →
      valAt' x ((W D).ι ⁻¹ᵁ L.U i) (σ.f i) = h i (x ≫ (W D).ι) := fun D => by
    refine _root_.GlobalTheory.CompanionTheory.Gaga.gagaSections_pure (W D).toScheme ((W D).ι ≫ s) D (hprop D) (hdim D) (resLB (W D).ι L)
      (isLB_resLB _ hL) (fun i x => h i (x ≫ (W D).ι)) ?_ ?_
    · intro i m B y hB hy hcond
      refine hhol i m B (fun b => y b ≫ (W D).ι) hB ?_ ?_
      · intro U f
        have := hy ((W D).ι ⁻¹ᵁ U) (((W D).ι.app U).hom f)
        simp only [val_comp]
        exact this
      · intro b hb
        refine ⟨by simpa using (hcond b hb).1, (hcond b hb).2⟩
    · intro i j x hx hU
      refine (hcomp i j (x ≫ (W D).ι) (by simpa using hx) hU).trans ?_
      rw [val_comp]
      rfl
  choose σ hσ using key
  have ex := fun i => glue W hc hd (L.U i) (fun D => (σ D).f i)
  choose b hb hbu using ex
  refine ⟨⟨b, fun i j => ?_⟩, fun i x hx hU => ?_⟩
  · refine (glue W hc hd (L.U i ⊓ L.U j) fun D => ((W D).ι.app _).hom
      ((X.presheaf.map (homOfLE inf_le_left).op).hom (b i))).unique (fun _ => rfl) fun D => ?_
    rw [map_mul, app_res, app_res, hb, hb]
    exact ((σ D).compat i j).symm
  · obtain ⟨D, x', rfl⟩ := exists_factor W hc x
    rw [val_comp, hb]
    exact hσ D i x' (by simpa using hx) hU

end GlobalTheory.CompanionTheory.Gaga
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TD

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem exists_hasSupport (hBZ : BernsteinZelevinskyFiniteness) (hG : GeometricLemma) (x : IrrGL (k := k)) :
    ∃ s, HasSupport x.rep s := by
  obtain ⟨s, d, σ, h⟩ := GlobalTheory.CuspSupportExist.main hBZ hG k x.1 (Irr.ofIrrRep x.2.rep)
  exact ⟨_, hasSupport_of_isCuspSupport h⟩

theorem map_univ_eq_sum {α : Type} {β : Type*} [Fintype α] (f : α → β) :
    Finset.univ.val.map f = ∑ a, ({f a} : Multiset β) := by
  rw [Finset.sum, ← Multiset.sum_map_singleton (Finset.univ.val.map f), Multiset.map_map]
  rfl

theorem hasSupport_of_isSubquotient_prodIrr {c N : ℕ} {y : Fin c → IrrGL (k := k)}
    {hd : ∑ a, (y a).1 = N} {t : Fin c → Multiset (IrrGL (k := k))} (ht : ∀ a, HasSupport (y a).rep (t a))
    {π : Representation ℂ (GL (Fin N) k) V} (hi : π.IsIrreducible) (h : IsSubquotient π (prodIrr y hd)) :
    HasSupport π (∑ a, t a) := by
  choose T u hu hc using ht
  have h3 := fun a => (hc a).2.2
  choose e' he' using h3
  let e := stdBlocks (fun a => (y a).1) hd
  have step1 : IsSubquotient (multiProd e fun a => (y a).rep)
      (multiProd e fun a => multiProd (e' a) fun b => (u a b).rep) :=
    GlobalTheory.CuspSupportExist.L_ind k _ _ _ e _ _ _ _ (isSmooth_piTensor fun a => isSmooth_parInd _ _)
      (GlobalTheory.CuspSupportExist.L_pit _ _ _ _ _ _ he')
  obtain ⟨E, hE⟩ := GlobalTheory.CuspSupportExist.L_stage k c N (fun a => (y a).1) e T (fun a b => (u a b).1) e' _
    (fun a b => (u a b).rep) fun a b => (u a b).2.rep.smooth
  refine ⟨∑ a, T a, fun c => u (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2, ?_, hi,
    fun c => (hc _).2.1 _, E, h.trans (step1.trans hE)⟩
  rw [map_univ_eq_sum, Equiv.sum_comp finSigmaFinEquiv.symm (fun p : (Σ a, Fin (T a)) => ({u p.1 p.2} : Multiset _)),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hu a, map_univ_eq_sum]

theorem exists_sum_of_jac (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL (k := k))} (hs : HasSupport π s) {r : ℕ} {d : Fin r → ℕ}
    (e' : (Σ j, Fin (d j)) ≃ Fin N) {τ : Representation ℂ (Levi k fun j => Fin (d j)) W} (hτ : τ.IsIrreducible)
    (hτs : IsSubquotient τ (GlobalTheory.SmGL.jac e' π)) (y : ∀ j, IrrRep (GL (Fin (d j)) k))
    (hy : ∀ j, IsSubquotient (y j).ρ (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W)) :
    ∃ t : Fin r → Multiset (IrrGL (k := k)), (∀ j, HasSupport (y j).ρ (t j)) ∧ s = ∑ j, t j := by
  obtain ⟨h, x, rfl, hi, hc, e, hsub⟩ := hs
  have hx : ∀ i, (x i).IsCusp := fun i => ⟨(hc i).1, (hc i).2.2⟩
  obtain ⟨b, f, g, c, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2 e e'
    (fun i => (x i).2.rep.smooth) (fun i => (x i).2.rep.hasFiniteLength) hτ
    (hτs.trans (GlobalTheory.JacquetExact.isSubquotient_jac e' (isSmooth_parInd _ _) hsub))
  choose J hJ0 hJ using fun i => exists_block_of_isCusp (hx i) (f i) (c i) (hrow i)
  let u : Fin h → Fin r → Multiset (IrrGL (k := k)) := fun i j => if j = J i then {x i} else 0
  have hu : ∀ i j, HasSupport (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr).rep (u i j) := by
    intro i j
    by_cases hj : j = J i
    · subst hj
      simp only [u, if_true]
      rw [hJ i]
      exact hasSupport_self (hx i)
    · obtain ⟨s', hs'⟩ := exists_hasSupport hBZ hG (IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr)
      simp only [u, if_neg hj]
      rwa [eq_zero_of_hasSupport (hJ0 i j hj) hs'] at hs'
  refine ⟨fun j => ∑ i, u i j, fun j => ?_, ?_⟩
  · have hd : ∑ i, b.1 i j = d j := by simpa using b.2.2 j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (c i j).ρ) j (y j).irr
      ((hy j).trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (c i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (c i j).ρ) (fun i => (c i j).smooth) fun i => (c i j).irr)
    exact hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (c i j).ρ (c i j).smooth (c i j).irr) (fun i => hu i j) (y j).irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  · rw [Finset.sum_comm]
    simp only [u, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Multiset.sum_map_singleton (Finset.univ.val.map x), Multiset.map_map]
    rfl

theorem eq_of_hasSupport (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) (N : ℕ) :
    ∀ (x : IrrGL (k := k)), x.1 = N → ∀ s t : Multiset (IrrGL (k := k)), HasSupport x.rep s → HasSupport x.rep t → s = t := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rintro x rfl s t hs ht
    rcases Nat.eq_zero_or_pos x.1 with h0 | hpos
    · rw [eq_zero_of_hasSupport h0 hs, eq_zero_of_hasSupport h0 ht]
    by_cases hc : IsCuspidal x.rep
    · rw [eq_singleton_of_isCusp ⟨hpos, hc⟩ hs, eq_singleton_of_isCusp ⟨hpos, hc⟩ ht]
    obtain ⟨r, d, e, hU, hJ⟩ : ∃ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin x.1), unipRad k e ≠ ⊥ ∧
        ¬ Subsingleton (Jacquet x.rep (unipRad k e)) := by
      by_contra! hn
      exact hc ⟨x.2.rep.smooth, hn⟩
    obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (GlobalTheory.SmGL.jac e x.rep)
      (not_subsingleton_iff_nontrivial.1 hJ)
    have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e x.2.rep.smooth)
    have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
      intro j
      obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
        (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
        (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
      exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
        (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
    choose y hy using hy
    obtain ⟨u, hu, rfl⟩ := exists_sum_of_jac hG hBZ hs e hτ hτs y hy
    obtain ⟨u', hu', rfl⟩ := exists_sum_of_jac hG hBZ ht e hτ hτs y hy
    refine Finset.sum_congr rfl fun j _ => ?_
    have hlt : d j < x.1 := by
      have hN : ∑ a, d a = x.1 := by simpa using Fintype.card_congr e
      obtain ⟨a, ha, hda⟩ : ∃ a, a ≠ j ∧ 0 < d a := by
        obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
        obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective p
        obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective q
        rw [blk_apply, blk_apply] at hpq
        by_cases haj : a = j
        · exact ⟨b, fun hb => hpq.ne (haj.trans hb.symm), q.pos⟩
        · exact ⟨a, haj, p.pos⟩
      have h1 := Finset.add_le_sum (s := Finset.univ) (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        (Finset.mem_univ j) ha
      omega
    exact ih (d j) hlt (IrrGL.of (y j).ρ (y j).smooth (y j).irr) rfl _ _
      ((hu j).of_equiv (IrrGL.equivOf _ _ _)) ((hu' j).of_equiv (IrrGL.equivOf _ _ _))

theorem hasSupport_unique (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {N : ℕ}
    {π : Representation ℂ (GL (Fin N) k) V} {s t : Multiset (IrrGL (k := k))} (hs : HasSupport π s)
    (ht : HasSupport π t) : s = t := by
  have φ := IrrGL.equivOf π hs.isSmooth hs.isIrreducible
  exact eq_of_hasSupport hG hBZ N (IrrGL.of π hs.isSmooth hs.isIrreducible) rfl s t (hs.of_equiv φ) (ht.of_equiv φ)

end GlobalTheory.CompanionTheory.Hypotheses₂.TD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeCharacterConductorExponentStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_conductor_exponent : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), ExpAt χ v m → multiplicity v.asIdeal (toHecke χ hu).conductor = m := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke | exact GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.multiplicity_conductor_toHecke <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeGaussSumLocalTermStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_gauss_sum_local_term : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), m ≠ 0 → ExpAt χ v m → ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) * psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) = gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | exact GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.InducedCellSemisimplification
section
theorem GlobalTheory.CompanionTheory.Glob.cellSemisimplification : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.CellSemisimplification k :=
  GlobalTheory.SmGL.CellSemis.cellSemisimplification _root_.GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaFunctionalEquation
section
noncomputable section

open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup GlobalTheory.CompanionTheory.PartialZeta
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {F : Type} [Field F] [NumberField F]

theorem coeff_inv_classHecke (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ) (J : (Ideal (𝓞 F))⁰) :
    ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) = ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) := by
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have h1 := coeff_inv_mul_coeff F (classHecke ψ) (standardOpenSubgroup_le_ker ψ) J hJ
  rw [coeff_classHecke ψ J hJ] at h1
  have h2 : ψ (Additive.ofMul (ClassGroup.mk0 J)⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 J)) = 1 := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, inv_mul_cancel, ofMul_one, AddChar.map_zero_eq_one]
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one h2) (h1.trans h2.symm)

def zetaOfClass (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).continuedLFunction s

def zetaOfClassInv (C : ClassGroup (𝓞 F)) (s : ℂ) : ℂ :=
  ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
    ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).continuedLFunction s

theorem isPartialZeta_of_indicator {ι : Type} [Fintype ι] (χ : ι → HeckeCharacter F) (c : ι → ℂ)
    (C : ClassGroup (𝓞 F)) (hU : ∀ i, standardOpenSubgroup F ≤ (χ i).toIdele.ker)
    (horth : ∀ J : (Ideal (𝓞 F))⁰,
      (ClassGroup.mk0 J = C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 1) ∧
      (ClassGroup.mk0 J ≠ C → ∑ i, c i * (χ i).coeff (J : Ideal (𝓞 F)) = 0)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (fun s => ∑ i, c i * (χ i).continuedLFunction s) := by
  classical
  refine ⟨?_, fun s hs => ?_⟩
  · exact DifferentiableOn.fun_sum fun i _ => (differentiableOn_continuedLFunction F (χ i) (hU i)).const_mul (c i)
  · have h1 : HasSum (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)))
        (∑ i, c i * (χ i).continuedLFunction s) := by
      refine hasSum_sum fun i _ => ?_
      rw [(χ i).continuedLFunction_eq hs]
      exact ((χ i).hasSum_LFunction hs).mul_left (c i)
    have hfac : ∀ I : Ideal (𝓞 F),
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) =
          (∑ i, c i * (χ i).coeff I) * (Ideal.absNorm I : ℂ) ^ (-s) := fun I => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
    let g : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} → Ideal (𝓞 F) :=
      fun J => (J.1 : Ideal (𝓞 F))
    have hg : Function.Injective g := fun a b hab =>
      Subtype.ext (Subtype.ext hab)
    have hsupp : ∀ I ∉ Set.range g,
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s)) = 0 := by
      intro I hI
      by_cases hbot : I = ⊥
      · subst hbot
        simp
      · let J : (Ideal (𝓞 F))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hbot⟩
        have hJ : ClassGroup.mk0 J ≠ C := fun h => hI ⟨⟨J, h⟩, rfl⟩
        rw [hfac, show I = (J : Ideal (𝓞 F)) from rfl, (horth J).2 hJ, zero_mul]
    have h2 := (hg.hasSum_iff hsupp).2 h1
    have h3 : (fun I : Ideal (𝓞 F) =>
        ∑ i, c i * ((χ i).coeff I * (Ideal.absNorm I : ℂ) ^ (-s))) ∘ g =
        fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
          ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s) := funext fun J => by
      simp only [Function.comp_apply]
      rw [hfac, show g J = (J.1 : Ideal (𝓞 F)) from rfl, (horth J.1).1 J.2, one_mul]
    rw [h3] at h2
    exact h2

theorem card_classGroup_ne_zero : (Fintype.card (ClassGroup (𝓞 F)) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem isPartialZeta_zetaOfClass (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClass C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => classHecke ψ) _ C (fun ψ => standardOpenSubgroup_le_ker ψ) fun J => ?_
  have hJ : (J : Ideal (𝓞 F)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero J
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) * (classHecke ψ).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if ClassGroup.mk0 J = C then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_classHecke ψ J hJ]
    ring_nf
  rw [e]
  constructor
  · intro h
    rw [if_pos h, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg h, mul_zero]

theorem isPartialZeta_zetaOfClassInv (C : ClassGroup (𝓞 F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C (zetaOfClassInv C) := by
  classical
  refine isPartialZeta_of_indicator (fun ψ => (classHecke ψ)⁻¹) _ C
    (fun ψ => standardOpenSubgroup_le_ker_inv F _ (standardOpenSubgroup_le_ker ψ)) fun J => ?_
  have e : ∑ ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ,
      ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C)) * ((classHecke ψ)⁻¹).coeff (J : Ideal (𝓞 F)) =
      (Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * (if C = ClassGroup.mk0 J then (Fintype.card (ClassGroup (𝓞 F)) : ℂ) else 0) := by
    rw [← sum_addChar_ofMul_mul_ofMul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [coeff_inv_classHecke ψ J, mul_assoc]
  rw [e]
  constructor
  · intro h
    rw [if_pos h.symm, inv_mul_cancel₀ card_classGroup_ne_zero]
  · intro h
    rw [if_neg (Ne.symm h), mul_zero]

theorem functionalEquation_classHecke [IsTotallyReal F] (ψ : AddChar (Additive (ClassGroup (𝓞 F))) ℂ)
    (D : (Ideal (𝓞 F))⁰) (hD : (D : Ideal (𝓞 F)) = differentIdeal ℤ (𝓞 F))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * (classHecke ψ).continuedLFunction s =
      ψ (Additive.ofMul (ClassGroup.mk0 D)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * ((classHecke ψ)⁻¹).continuedLFunction (1 - s)) := by
  have hU := standardOpenSubgroup_le_ker ψ
  have h := fe_of_parts F (classHecke ψ) (discrNormConductor_eq_dF_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ hU)
    (gammaFactor_eq_of_unramified F _ (standardOpenSubgroup_le_ker_inv F _ hU))
    (rootNumber_eq_coeff_different F _ hU) s h1 h2
  rw [← hD, coeff_classHecke ψ _ (nonZeroDivisors.coe_ne_zero D)] at h
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂

theorem GlobalTheory.CompanionTheory.Hypotheses₂.partialZetaFunctionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation := by
  intro F _ _ _ C C' D hD hC
  refine ⟨GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv C',
    GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClass C, GlobalTheory.CompanionTheory.Hypotheses₂.isPartialZeta_zetaOfClassInv C', fun s h1 h2 => ?_⟩
  rw [GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClass, GlobalTheory.CompanionTheory.Hypotheses₂.zetaOfClassInv, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have h := GlobalTheory.CompanionTheory.Hypotheses₂.functionalEquation_classHecke ψ D hD s h1 h2
  have e : ψ (Additive.ofMul C⁻¹) * ψ (Additive.ofMul (ClassGroup.mk0 D)) = ψ (Additive.ofMul C') := by
    rw [← AddChar.map_add_eq_mul, ← ofMul_mul, ← hC, inv_mul_cancel_left]
  calc _ = ((Fintype.card (ClassGroup (𝓞 F)) : ℂ)⁻¹ * ψ (Additive.ofMul C⁻¹)) *
        ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F *
          (GlobalTheory.CompanionTheory.PartialZeta.classHecke ψ).continuedLFunction s) := by ring
    _ = _ := by
      rw [h, ← e]
      ring
end
end

