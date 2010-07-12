<?php

$pages = array('Accueil', 'Équipe', 'Résultats', 'Documentation');

if (isset ($_GET['page'])) { $page = (int) $_GET['page']; }
else { $page=0; }

include('top.inc.php');

if($page == 0)
{

?>

<div id="news"><h3>News</h3>

<p>[07 avril] The first release is now available ! You can download it <a href="http://sourceforge.net/projects/coqtail/files/">here</a>.</p>
</div>

<h2>Origine &amp; Objectifs</h2>

<p>Le projet <a href="https://sourceforge.net/projects/coqtail/">COQTAIL</a> est le fils biologique du groupe de travail `Preuves` du projet 
<a href="http://graal.ens-lyon.fr/coquille">COQUILLE</a>. Il se fonde donc sur 
l'intégralité des résultats obtenus lors du semestre de développement de COQUILLE.</p>

<p>En plus d'implémenter des outils permettant une formalisation aisée des mathématiques
abordées en classes préparatoires, ce projet tâchera également de démontrer des résultats
de niveau licence.</p> 

<h2>Axes de développements</h2>

<ul>
	<li>Analyse (réelle et complexe)</li>
	<li>Arithmétique</li>
	<li>Calculabilité</li>
	<li>Implémentation de &#x2102;</li>
	<li>Logique, expressivité de l'axiomatique de &#x211d;</li>
	<li>Topologie</li>
</ul>
<?php

}

elseif($page == 1)
{

?>
Membres du laboratoire junior :
<ul>
  <li> Marc Lasson, responsable du laboratoire junior </li>
  <li> Guillaume Allais </li>
  <li> Marthe Bonamy </li>
  <li> Sylvain Dailler </li>
  <li> Jean-Marie Madiot </li>
  <li> Pierre-Marie Pédrot </li>
</ul>

Membres en rapport avec le projet :
<ul>
	<li><a href="http://sourceforge.net/project/memberlist.php?group_id=298939">Équipe actuelle</a> (sur Sourceforge)</li>
	<li><a href="http://graal.ens-lyon.fr/coquille/index.php?page=team">Ancienne équipe</a> (projet COQUILLE)</li>
</ul>
<?php

}

elseif($page == 2)
{

?>
<h2>Quelques jolis résultats</h2>
<ul>
	<li>&#x211d; est indénombrable</li>
	<li>L'axiomatique des réels implique le principe de Markov</li>
	<li>Problème de Bâle (<em>1+1/2²+1/3²+1/4²+...= &pi;²/6</em>)</li>
	<li>Formule de Stirling (approximation de <em>n!</em>)</li>
</ul>

<h2>De nouvelles bibliothèques</h2>

<ul>
	<li>Arithmétique</li>
	<li>Topologie (définition de nombreuses typeclass de base, recherche de définitions les plus générales possibles)</li>
	<li>Bibliothèques ordonnées de résultats sur les suites et séries réelles et les suites complexes</li>
	<li>Définition et manipulation des complexes et des concepts de base</li>
	<li>Formalisation des séries entières et développements sur les rayons de convergence</li>
</ul>
<?php

}

elseif($page == 3)
{
if ($doc) { include($doc); }
else
{
?>
<h2>Liens</h2>
<ul>
	<li><a href="http://sourceforge.net/apps/mediawiki/coqtail/index.php?title=Main_Page">Wiki du projet</a></li>
	<li><a href="http://graal.ens-lyon.fr/coquille/coqdoc/">Documentation de COQUILLE</a></li>
</ul>
<?php
include ('doc/index.html');
}
}
include('foot.inc.php')
?>
