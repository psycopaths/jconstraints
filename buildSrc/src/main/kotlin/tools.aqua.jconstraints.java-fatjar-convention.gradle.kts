/*
 * Copyright 2015 United States Government, as represented by the Administrator
 *                of the National Aeronautics and Space Administration. All Rights Reserved.
 *           2017-2021 The jConstraints Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import com.github.jengelman.gradle.plugins.shadow.tasks.ShadowJar
import org.gradle.api.publish.maven.MavenPublication
import org.gradle.api.publish.tasks.GenerateModuleMetadata
import org.gradle.kotlin.dsl.get

plugins {
    id("tools.aqua.jconstraints.java-convention")
    id("com.github.johnrengelman.shadow") apply (false)
}

val fatJar by tasks.registering(ShadowJar::class) {
    archiveClassifier.set("with-all")
    from(sourceSets.main.map { it.output })
    configurations = listOf(project.configurations["runtimeClasspath"])
}

tasks {
    assemble {
        dependsOn(fatJar)
    }

    withType<ShadowJar> {
        manifest {
            attributes["Main-Class"] = "gov.nasa.jpf.constraints.smtlibUtility.SMTCommandLine"
        }
        dependencies {
            exclude("*.smt2", "*.smt2.*")
            exclude("APIExample.class")
        }
        relocate("org.smtlib", "tools.aqua.redistribution.org.smtlib")
    }

    withType<GenerateModuleMetadata> {
        enabled = false
    }
}

publishing {
    publications {
        create<MavenPublication>("mavenJavaFat") {
            artifact(fatJar) { classifier = null }
            artifactId = "${project.name}-all"
            pom {
                name.set(provider { project.description?.split(' ')?.first()?.plus(" Fat JAR") })
                description.set(provider { project.description?.plus(" (including all dependencies)") })
            }
        }
    }
}
