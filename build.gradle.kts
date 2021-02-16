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

import org.gradle.api.tasks.testing.logging.TestLogEvent.FAILED
import org.gradle.api.tasks.testing.logging.TestLogEvent.PASSED
import org.gradle.api.tasks.testing.logging.TestLogEvent.SKIPPED
import org.gradle.api.tasks.testing.logging.TestLogEvent.STANDARD_ERROR
import java.time.LocalDate.now

plugins {
    antlr
    `java-library`
    `maven-publish`
    id("com.github.johnrengelman.shadow") version "5.2.0"
    id("com.github.sherter.google-java-format") version "0.9"
    id("org.cadixdev.licenser") version "0.5.0"
}

java {
    toolchain {
        languageVersion.set(JavaLanguageVersion.of(8))
    }
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"

repositories {
    mavenCentral()
    maven { url = uri("https://jitpack.io") }
}

dependencies {
    antlr("org.antlr:antlr:3.5.2")
    implementation("com.google.guava:guava:14.0.1")
    implementation("com.github.tudo-aqua:jSMTLIB:5c11ee5")
    implementation("commons-cli:commons-cli:1.4")
    implementation("dk.brics:automaton:1.12-1")
    implementation("org.antlr:antlr-runtime:3.5.2")
    implementation("org.apache.commons:commons-math3:3.6.1")
    testImplementation("org.testng:testng:6.8")
}

group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "jConstraints"


license {
    header = project.file("contrib/license-header.txt")
    ext["year"] = now().year

    exclude("**/*.smt2", "**/*.txt")

    tasks {
        create("buildFiles") {
            files = project.files("build.gradle.kts", "settings.gradle.kts")
        }
    }
}


tasks.test {
    useTestNG() {
        useDefaultListeners = true
        includeGroups = setOf("base")
    }
    testLogging {
        events(FAILED, STANDARD_ERROR, SKIPPED, PASSED)
    }
}

tasks.shadowJar {
    archiveFileName.set(
        "${archiveBaseName.get()}-${archiveClassifier.get()}-${archiveVersion.get()}.${archiveExtension.get()}"
    )
}

publishing {
    publications {
        create<MavenPublication>("mavenJava") {
            artifactId = "jconstraints"
            from(components["java"])
            pom {
                name.set("jConstraints")
                description.set("jConstraints is a library for managing SMT constraints in Java.")
                url.set("https://github.com/tudo-aqua/jconstraints")
                licenses {
                    license {
                        name.set("Apache-2.0")
                        url.set("https://www.apache.org/licenses/LICENSE-2.0.txt")
                    }
                }
                developers {
                    developer {
                        id.set("mmuesly")
                        name.set("Malte Mues")
                        email.set("mail.mues@gmail.com")
                    }
                    developer {
                        id.set("fhowar")
                        name.set("Falk Howar")
                    }
                }
                scm {
                    connection.set("https://github.com/tudo-aqua/jconstraints.git")
                    url.set("https://github.com/tudo-aqua/jconstraints")
                }
            }
        }
        create<MavenPublication>("publishMaven") {
            artifact(tasks["shadowJar"]) {
                classifier = null
            }
            artifactId = "jconstraints-all"

        }
    }
}
